-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_6_11
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_6_11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:45:41.028444+00:00
-- url     : https://prove2.me/theorems/9348ed5c-e557-4d74-9654-c7e392af87fc
-- title:
--   Theorem 6.11: seven equivalent eventual channel properties
-- statement:
--   Let $\tau$ be a unital quantum channel on $M_d$, $d\ge1$, and let $\mathcal P(\tau)$ be its peripheral space. The following seven properties are equivalent:
--
--   1. $\tau$ is eventually MTD.
--   2. $\tau$ is eventually EB.
--   3. $\tau$ is eventually PPT.
--   4. $\tau$ is eventually 2-copositive.
--   5. Some positive power has range contained in $\mathcal P(\tau)'$.
--   6. $\bigcap_{n\ge1}\operatorname{Range}(\tau^n)\subseteq\mathcal P(\tau)'$.
--   7. For every nonzero $\lambda\in\mathbb C$,
--   $$\ker(\tau-\lambda\operatorname{id})\subseteq\mathcal P(\tau)'.$$
--
--   Eventually means that the property holds for every iterate beyond some threshold $n_0\ge1$. No restriction is imposed at the zero eigenvalue, and neither primitivity nor diagonalizability is assumed. This is the discrete-time capstone characterization.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 24, Theorem 6.11

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 6.11, PDF pp.24,25. -/
theorem theorem_6_11 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    (Eventually MTD t ↔ Eventually EB t) ∧
    (Eventually MTD t ↔ Eventually PPT t) ∧
    (Eventually MTD t ↔ Eventually TwoCopositive t) ∧
    (Eventually MTD t ↔ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ X : Mat d, applyMap (t^n0) X ∈ commutant (peripheral t : Set (Mat d))) ∧
    (Eventually MTD t ↔ stableRange t ⊆ commutant (peripheral t : Set (Mat d))) ∧
    (Eventually MTD t ↔ ∀ a : ℂ, a ≠ 0 → ∀ X : Mat d,
      applyMap t X = a • X → X ∈ commutant (peripheral t : Set (Mat d))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
