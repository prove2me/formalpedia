-- Prove2me | Theorems.Thm_SmoothBerr_theorem_5_1
-- name    : SmoothBerr.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:00.417192+00:00
-- url     : https://prove2.me/theorems/bf2d6f2f-a64f-4465-ae79-d0e71c58b324
-- title:
--   Theorem 5.1 — hidden Gaussian theorem (corrected: linearly independent queries)
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries. A (deterministic, possibly adaptive) paired matvec algorithm with $t\le n$ steps computes left queries $u_1,\dots,u_t$ and right queries $v_1,\dots,v_t$, producing the transcript $\mathcal T_t=(u_i,A^\top u_i,v_i,Av_i)_{i=1}^t$. Assume that, almost surely, $u_1,\dots,u_t$ are linearly independent and $v_1,\dots,v_t$ are linearly independent. Then there are matrices $B_{11}\in\mathbb R^{t\times t}$, $B_{12}\in\mathbb R^{t\times(n-t)}$, $B_{21}\in\mathbb R^{(n-t)\times t}$ and orthogonal matrices $R,S\in\mathbb R^{n\times n}$, all measurable functions of $\mathcal T_t$, such that almost surely
--   $$
--   R^\top A S=\begin{bmatrix}B_{11}&B_{12}\\ B_{21}&G\end{bmatrix},
--   $$
--   where the block $G\in\mathbb R^{(n-t)\times(n-t)}$ is independent of $\mathcal T_t$ and has iid $\mathcal N(0,1)$ entries.
--
--   In words: after $t$ adaptive paired matvecs, an $(n-t)\times(n-t)$ Gaussian matrix remains completely hidden from the algorithm. This is the information-theoretic core of the lower bounds in the paper.
--
--   **Formalization Note** "Constructed deterministically from $\mathcal T_t$" is measurability in the transcript; "conditioned on $\mathcal T_t$, $G$ has iid $\mathcal N(0,1)$ entries" is joint independence of $G$ from $\mathcal T_t$ together with the law of $G$. The algorithm's input and seed are fixed.
--
--   Differences from the source:
--   - correction: arbitrary (possibly adaptive) queries u_i, v_i → a.s. the u_i are linearly independent and the v_i are linearly independent; reason: false as printed: n = t = 1 with u₁ = v₁ = 0 gives a constant transcript, R, S ∈ {±1}, and B₁₁ = ±A would be a.s. constant while A ∼ N(0,1); the proof assumes orthonormal queries "without loss of generality", which changes the algorithm, not the statement
--   - encoding: blocks of sizes t and n − t → hypothesis t ≤ n; reason: needed to form the blocks; implied by linear independence of t vectors in ℝⁿ
--   - reading: a paired matvec algorithm → a PairedMatvecAlg with fixed input x and fixed seed ω (a deterministic algorithm); reason: the statement has no randomness besides A; a randomized algorithm is covered seed by seed
--   - encoding: B_ij, R, S constructed deterministically from T_t; conditioned on T_t, B_ij deterministic and G with iid N(0,1) entries → R, S, B_ij measurable functions of the transcript; G (the lower-right block of R(T_t)ᵀAS(T_t)) independent of T_t with law gaussianMatrix (n−t) (n−t); reason: a conditional law of G that does not depend on T_t is the same as independence plus that law
--   - encoding: the block layout [B_11 B_12; B_21 G] → blockView: first t indices, last n − t indices; reason: R and S are existential, so the order of the basis is a convention
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 5.1, pp.9–10

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SmoothBerr_PairedMatvecAlg
import Definitions.Def_SmoothBerr_blockView

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Theorem 5.1 (Hidden Gaussian theorem), corrected: linearly independent queries** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…,
Theorem 5.1, pp.9–10).

Let `A ∈ ℝ^{n×n}` have iid `N(0,1)` entries, and run a (deterministic, possibly adaptive) paired
matvec algorithm with `t ≤ n` steps against `A`, producing the transcript
`T_t = (u_i, Aᵀu_i, v_i, Av_i)_{i<t}`. Suppose that almost surely the left queries `u_i` are
linearly independent and the right queries `v_i` are linearly independent. Then there are
measurable maps `R, S` from transcripts to orthogonal `n × n` matrices and measurable maps
`B₁₁, B₁₂, B₂₁` from transcripts to `t × t`, `t × (n−t)`, `(n−t) × t` matrices such that, almost
surely, `R(T_t)ᵀ A S(T_t) = [B₁₁(T_t) B₁₂(T_t); B₂₁(T_t) G]`, where the lower-right block `G` is
independent of `T_t` and has iid `N(0,1)` entries.

**Formalization Note** The algorithm is deterministic: its input `x` and seed `ω` are fixed.
"All constructed deterministically from `T_t`" is: `R, S, B_{ij}` are measurable functions of
the transcript. "Conditioned on `T_t`, … `G` has iid `N(0,1)` entries" is: `G` is independent of
`T_t` (jointly, as a random matrix) and its law is `gaussianMatrix (n−t) (n−t)`. The blocks are
read with `blockView` (first `t` indices, last `n − t` indices). Random matrices are functions
`Fin n → Fin n → ℝ` (the sample space of `gaussianMatrix`), viewed with `Matrix.of`. The
hypothesis of linearly independent queries is a correction: as printed, with `n = t = 1` and
`u₁ = v₁ = 0` the transcript is constant and `B₁₁ = ±A` cannot be a function of it. -/
theorem theorem_5_1 {n t : ℕ} {ι Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (alg : PairedMatvecAlg n t ι Ω β) (x : ι) (ω : Ω) (htn : t ≤ n)
    (hlin : ∀ᵐ a ∂(gaussianMatrix n n),
      LinearIndependent ℝ (fun k => (alg.queries (Matrix.of a) x ω k).1) ∧
      LinearIndependent ℝ (fun k => (alg.queries (Matrix.of a) x ω k).2)) :
    ∃ (R S : (Fin t → TranscriptEntry n) → (Fin n → Fin n → ℝ))
      (B₁₁ : (Fin t → TranscriptEntry n) → (Fin t → Fin t → ℝ))
      (B₁₂ : (Fin t → TranscriptEntry n) → (Fin t → Fin (n - t) → ℝ))
      (B₂₁ : (Fin t → TranscriptEntry n) → (Fin (n - t) → Fin t → ℝ)),
      Measurable R ∧ Measurable S ∧ Measurable B₁₁ ∧ Measurable B₁₂ ∧ Measurable B₂₁ ∧
      (∀ T, Matrix.of (R T) ∈ Matrix.orthogonalGroup (Fin n) ℝ) ∧
      (∀ T, Matrix.of (S T) ∈ Matrix.orthogonalGroup (Fin n) ℝ) ∧
      (∀ᵐ a ∂(gaussianMatrix n n),
        (blockView htn ((Matrix.of (R (alg.transcript (Matrix.of a) x ω)))ᵀ * Matrix.of a *
            Matrix.of (S (alg.transcript (Matrix.of a) x ω)))).toBlocks₁₁ =
          Matrix.of (B₁₁ (alg.transcript (Matrix.of a) x ω)) ∧
        (blockView htn ((Matrix.of (R (alg.transcript (Matrix.of a) x ω)))ᵀ * Matrix.of a *
            Matrix.of (S (alg.transcript (Matrix.of a) x ω)))).toBlocks₁₂ =
          Matrix.of (B₁₂ (alg.transcript (Matrix.of a) x ω)) ∧
        (blockView htn ((Matrix.of (R (alg.transcript (Matrix.of a) x ω)))ᵀ * Matrix.of a *
            Matrix.of (S (alg.transcript (Matrix.of a) x ω)))).toBlocks₂₁ =
          Matrix.of (B₂₁ (alg.transcript (Matrix.of a) x ω))) ∧
      IndepFun (fun a => alg.transcript (Matrix.of a) x ω)
        (fun a => fun i j => (blockView htn ((Matrix.of (R (alg.transcript (Matrix.of a) x ω)))ᵀ *
            Matrix.of a * Matrix.of (S (alg.transcript (Matrix.of a) x ω)))).toBlocks₂₂ i j)
        (gaussianMatrix n n) ∧
      (gaussianMatrix n n).map
          (fun a => fun i j => (blockView htn ((Matrix.of (R (alg.transcript (Matrix.of a) x ω)))ᵀ *
            Matrix.of a * Matrix.of (S (alg.transcript (Matrix.of a) x ω)))).toBlocks₂₂ i j) =
        gaussianMatrix (n - t) (n - t) := by sorry

end SmoothBerr
