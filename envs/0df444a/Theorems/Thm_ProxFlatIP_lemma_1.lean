-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_1
-- name    : ProxFlatIP.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:25.27736+00:00
-- url     : https://prove2.me/theorems/4e971c15-5f4d-413c-87f0-eb09ec163549
-- title:
--   Lemma 1 (corrected: $\hat\alpha^\top P=\alpha^\top$ on $\ker A_I$) — a slice is a full-dimensional instance in dimension $d$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, $b\in\mathbb Z^m$ with $P(A,b)\cap\mathbb Z^n\ne\emptyset$, and $\alpha\in\mathbb Z^n$ such that $\max\{\alpha^\top x:x\in P(A,b)\}$ is attained. Let $I\subseteq[m]$ be admissible, with the linear span of $P_I(A,b)$ equal to $\ker A_I$, of dimension $d$.
--
--   Then there is $T\in\mathbb Z^{d\times n}$ such that $x\mapsto Tx$ restricts to a linear bijection $\ker A_I\to\mathbb R^d$, maps $\ker A_I\cap\mathbb Z^n$ onto $\mathbb Z^d$, and maps $P_I(A,b)$ onto $P(\hat A,\hat b)$ for some $\hat A\in\mathbb Z^{(m-n+d)\times d}$ of full column rank and $\hat b\in\mathbb Z^{m-n+d}$. Moreover there is a unique $\hat\alpha\in\mathbb Z^d$ with $\hat\alpha^\top Tx=\alpha^\top x$ for all $x\in\ker A_I$, and
--   $$\kappa_I(A,b,\alpha)=\kappa_d(\hat A,\hat b,\hat\alpha).$$
--
--   This is the dimension reduction: every slice of an instance is a full-dimensional instance in lower dimension with the same parameter $\kappa$.
--
--   **Formalization Note** The paper's matrix $P$ is called $T$, since $P$ is the polyhedron here. $P_I$ is defined only for admissible $I$, so $d\ge1$.
--
--   Differences from the source:
--   - correction: α̂ ∈ Z^d is the unique vector satisfying α̂⊤P = α⊤ → α̂⊤Tx = α⊤x for all x ∈ ker A_I; reason: as a matrix identity it is false: for A = (I ; −I), b = (1,1,1,1), I = {1}, α = e₁, the span of P_I is ker A_I, but any α̂ with α̂⊤Tx = α⊤x on ker A_I is 0 and 0 ≠ e₁; the proof derives only the identity on ker A_I (eq. (3))
--   - generalization: Â ∈ Z^{(m−n+d)×d} → also Â has full column rank; reason: it follows from the proof, and it makes κ_d(Â,b̂,α̂) an instance of the setting of the paper
--   - encoding: I ⊆ [m] indexes linearly independent rows of A → I is admissible (|I| ≤ n − 1 and rank A_I = |I|); reason: P_I is defined only for such I (p.4); the excluded |I| = n has ker A_I = {0}
--   - encoding: κ_I is the number with max_{x∈P_I} α⊤x = κ_I·Δ^α_I(A), with no value when Δ^α_I(A) = 0 → κ_I = 0 there (Lean's x/0 = 0); reason: Δ^α_I(A) = 0 only when α lies in the row space of A_I, so α⊤x = 0 on P_I and (2) holds for every κ_I; no instance with Δ^α_I(A) > 0 changes
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 1, p.5

import Mathlib
import Definitions.Def_ProxFlatIP_Kappa

open Matrix

namespace ProxFlatIP

/-- **Lemma 1** (corrected: `α̂⊤P = α⊤` on `ker A_I`) (arXiv:2211.14941v1, Lemma 1, p.5). Suppose
`max{α⊤x : x ∈ P}` is attained, and `I` indexes linearly independent rows of `A` such that the linear
span of `P_I` is `ker A_I`, of dimension `d`. Then there is `T ∈ ℤ^{d×n}` such that `x ↦ Tx` restricts
to a linear bijection `ker A_I → ℝᵈ`, maps `ker A_I ∩ ℤⁿ` onto `ℤᵈ`, and maps `P_I(A,b)` onto
`P(Â,b̂)` for some `Â ∈ ℤ^{(m−n+d)×d}` of full column rank and `b̂ ∈ ℤ^{m−n+d}`. There is a unique
`α̂ ∈ ℤᵈ` with `α̂⊤Tx = α⊤x` for all `x ∈ ker A_I`, and `κ_I(A,b,α) = κ_d(Â,b̂,α̂)`.

**Formalization Note.** The paper's matrix `P` is called `T` here. The paper writes `α̂⊤P = α⊤`, which
holds only on `ker A_I`: for `α` a nonzero row of `A_I`, the paper's `α̂` is `0`. `P_I` is defined
only for admissible `I` (p.4), so `d ≥ 1`. Full column rank of `Â` follows from the proof and makes
`κ_d(Â,b̂,α̂)` an instance of the paper's setting. "IP feasible" is the standing assumption of §2.
`m − n` is not truncated, since full column rank gives `n ≤ m`. -/
theorem lemma_1 {m n d : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (b : Fin m → ℤ)
    (hIP : IsIPFeasible A b) (α : Fin n → ℤ)
    (hmax : ∃ x ∈ Poly A b, ∀ y ∈ Poly A b, castVec α ⬝ᵥ y ≤ castVec α ⬝ᵥ x)
    (I : Finset (Fin m)) (hI : Admissible A I)
    (hspan : (Submodule.span ℝ (PI A b I) : Set (Fin n → ℝ)) = kerRows A I)
    (hd : dimLin (kerRows A I) = d) :
    ∃ (T : Matrix (Fin d) (Fin n) ℤ) (A' : Matrix (Fin (m - n + d)) (Fin d) ℤ)
      (b' : Fin (m - n + d) → ℤ) (α' : Fin d → ℤ),
      Set.BijOn (fun x => realMat T *ᵥ x) (kerRows A I) Set.univ ∧
      (fun x => realMat T *ᵥ x) '' (kerRows A I ∩ {x | IsIntegralPt x}) = {y | IsIntegralPt y} ∧
      (fun x => realMat T *ᵥ x) '' PI A b I = Poly A' b' ∧
      FullColRank A' ∧
      (∀ x ∈ kerRows A I, castVec α' ⬝ᵥ (realMat T *ᵥ x) = castVec α ⬝ᵥ x) ∧
      (∀ β : Fin d → ℤ,
        (∀ x ∈ kerRows A I, castVec β ⬝ᵥ (realMat T *ᵥ x) = castVec α ⬝ᵥ x) → β = α') ∧
      kappaI A b α I = kappaD A' b' α' d := by sorry

end ProxFlatIP
