-- Prove2me | Theorems.Thm_SteurerHDX_theorem_1_5
-- name    : SteurerHDX.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:59.889901+00:00
-- url     : https://prove2.me/theorems/afa14df6-a8e2-4265-a7bb-6cec6ace48d9
-- title:
--   Theorem 1.5: nonnegative unit vectors with average correlation $n^{-1+o(1)}$ and no linear-sized $(\log n)^{-1/4+o(1)}$-separated sets
-- statement:
--   This is the paper's main result, refuting Steurer's conjecture in a strong sense.
--
--   For every $0<\beta<1/2$ there are infinitely many $n>0$ and nonnegative unit vectors $v_1,\dots,v_n$ (in some Euclidean space) satisfying the **squared triangle inequality**
--   $$\|v_i-v_j\|^2\le\|v_i-v_k\|^2+\|v_k-v_j\|^2\qquad(1\le i,j,k\le n)$$
--   such that
--   $$\mathbb E_{i,j}|\langle v_i,v_j\rangle|\le n^{-1+o(1)},$$
--   and every two disjoint sets of vectors $A,B$ with $|A|,|B|\ge\beta n$ contain $v_i\in A$ and $v_j\in B$ with
--   $$\|v_i-v_j\|_2^2\le O_\beta\bigl((\log n)^{-1/4+o(1)}\bigr).$$
--
--   Steurer conjectured that average correlation $n^{-\varepsilon}$ forces linear-sized sets separated by a constant; the theorem shows that even average correlation $n^{-1+o(1)}$ allows every pair of linear-sized sets to come within $(\log n)^{-1/4+o(1)}$.
--
--   **Formalization Note** The family is a strictly increasing sequence of sizes $N_m$ with a configuration for each; the $o(1)$ terms are real sequences $e_1(m),e_2(m)\to0$ and $O_\beta$ is a constant $C>0$ chosen after $\beta$ and before the sequence.
--
--   Differences from the source:
--   - reading: infinitely many n > 0; n^{−1+o(1)}; O_β((log n)^{−1/4+o(1)}) → a strictly increasing sequence N with 0 < N m; real sequences e₁, e₂ tending to 0 with bounds N^{−1+e₁(m)} and C·(log N)^{−1/4+e₂(m)}; C > 0 chosen after β and before the sequence; reason: the standard meaning of the asymptotic notation along the family the theorem asserts
--   - encoding: unit vectors in an unspecified Euclidean space; E_{i,j}; sets of vectors; ‖·‖₂² → vectors in EuclideanSpace ℝ (Fin D) for some D; (1/n²) Σ_{i,j} over ordered pairs; Finset (Fin n) of indices; ‖·‖ ^ 2; reason: Lean convention; same instances
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Theorem 1.5, p.2; Eq. (1.1), p.1

import Mathlib
open Filter Topology

namespace SteurerHDX

/-- **Theorem 1.5 (refutation of Steurer's conjecture).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Theorem 1.5, p.2: "For every
0 < β < 1/2, there are infinitely many n > 0 and nonnegative unit vectors v₁, …, v_n satisfying
squared triangle inequality (1.1) such that E_{i,j}|⟨vᵢ, vⱼ⟩| ≤ n^{−1+o(1)}, and every two disjoint
sets of vectors A, B with |A|, |B| ≥ βn contain vᵢ ∈ A and vⱼ ∈ B with
‖vᵢ − vⱼ‖₂² ≤ O_β(log n)^{−1/4+o(1)}."  (1.1), p.1: ‖vᵢ − vⱼ‖² ≤ ‖vᵢ − v_k‖² + ‖v_k − vⱼ‖².

**Formalization Note.** "Infinitely many n" is a strictly increasing sequence `N m` of sizes with
a family of vectors for each; the two o(1) terms are real sequences `e₁ m`, `e₂ m` tending to 0
along it; O_β is a constant C > 0 chosen after β and before the sequence. The vectors live in
`EuclideanSpace ℝ (Fin (D m))` for some dimension D m; E_{i,j} is the uniform average over ordered
pairs (diagonal included); sets of vectors are sets of indices. Both bounds hold for the same
vectors. -/
theorem theorem_1_5 :
    ∀ β : ℝ, 0 < β → β < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
    ∃ (N D : ℕ → ℕ) (v : (m : ℕ) → Fin (N m) → EuclideanSpace ℝ (Fin (D m))) (e₁ e₂ : ℕ → ℝ),
      StrictMono N ∧ Tendsto e₁ atTop (𝓝 0) ∧ Tendsto e₂ atTop (𝓝 0) ∧
      ∀ m, 0 < N m ∧
        (∀ i k, 0 ≤ v m i k) ∧ (∀ i, ‖v m i‖ = 1) ∧
        (∀ i j k, ‖v m i - v m j‖ ^ 2 ≤ ‖v m i - v m k‖ ^ 2 + ‖v m k - v m j‖ ^ 2) ∧
        (1 / (N m : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (v m i) (v m j)| ≤ (N m : ℝ) ^ (-1 + e₁ m) ∧
        ∀ A B : Finset (Fin (N m)), Disjoint A B →
          β * N m ≤ A.card → β * N m ≤ B.card →
          ∃ i ∈ A, ∃ j ∈ B,
            ‖v m i - v m j‖ ^ 2 ≤ C * Real.log (N m) ^ (-(1 / 4 : ℝ) + e₂ m) := by sorry

end SteurerHDX
