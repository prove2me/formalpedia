-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_canonical_box_weighted_face_minimum
-- name    : WeierstrassEllipticZeta.canonical_box_weighted_face_minimum
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T21:13:23.085202+00:00
-- url     : https://prove2.me/theorems/a5e53d27-5ba4-44cd-9083-c47ee47bd172
-- title:
--   Canonical coordinate boxes minimize the weighted face count
-- statement:
--   Let σ be a finite coordinate set with decidable equality, and let d,t:σ→ℕ. Among coordinate boxes b satisfying d_i≤b_i and t_i≤b_i+1, there is a box whose side lengths are
--
--   $$b_i+1=\max(d_i+1,t_i).$$
--
--   Its degree-weighted face count is exactly
--
--   $$\Phi(d,t)=\sum_i d_i\prod_{j\ne i}\max(d_j+1,t_j),$$
--
--   and this is at most the weighted face count of every other admissible box. The theorem provides the box, both admissibility conditions, its side-length formula, the exact count, and the minimum inequality. It includes zero degree or count data and an empty coordinate set.
-- source:
--   Derived exact box minimization for the frontier https://prove2.me/theorems/7474c39b-a6ed-4850-82c1-ddace253bc6b. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The combinatorial certificate is derived using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Data/Finsupp/Defs.lean (equivFunOnFinite) and Algebra/Order/BigOperators/Group/Finset.lean (prod_le_prod', sum_le_sum), with elementary natural-number order and truncated subtraction. The new geometric child is equivalent to the selected frontier: the canonical side length is max(degree+1, contact order times coordinate-value count). The uniform geometric estimate and the main mission theorem remain open.

import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Classical

noncomputable section

theorem WeierstrassEllipticZeta.canonical_box_weighted_face_minimum
    (σ : Type*) [Fintype σ] [DecidableEq σ] (d t : σ → ℕ) :
    ∃ b : σ →₀ ℕ,
      (∀ i : σ, d i ≤ b i) ∧
      (∀ i : σ, t i ≤ b i + 1) ∧
      (∀ i : σ, b i + 1 = max (d i + 1) (t i)) ∧
      (∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i, (b j + 1)) =
        ∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i,
          max (d j + 1) (t j) ∧
      ∀ b' : σ →₀ ℕ,
        (∀ i : σ, d i ≤ b' i) → (∀ i : σ, t i ≤ b' i + 1) →
          (∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i,
            max (d j + 1) (t j)) ≤
          ∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i, (b' j + 1) := by sorry
