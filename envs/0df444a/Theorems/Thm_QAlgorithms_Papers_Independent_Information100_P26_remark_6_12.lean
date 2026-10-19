-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_6_12
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_6_12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:58:02.40117+00:00
-- url     : https://prove2.me/theorems/cb5b6786-cb32-4ed1-91c3-4ef867fc1d37
-- title:
--   Remark 6.12: stable ranges and nonzero generalized eigenspaces
-- statement:
--   For a unital channel $\tau$ on $M_d$, $d\ge1$, the descending ranges stabilize by the ambient dimension:
--   $$\bigcap_{n\ge1}\operatorname{Range}(\tau^n)=\bigcap_{n=1}^{d^2}\operatorname{Range}(\tau^n)=\operatorname{span}_{\mathbb C}\{X:(\tau-\lambda\operatorname{id})^kX=0,\ \lambda\ne0,\ k\ge1\}.$$
--   Thus inclusion of the stable range in $\mathcal P(\tau)'$ is equivalent to commutation for all generalized eigenvectors at nonzero eigenvalues. This supplies the generalized-eigenvector reading of condition (6) in Theorem 6.11.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 25, Remark 6.12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 6.12, PDF pp.25. The source next cites Example 6.18 as a kernel example, but that depolarizing map is invertible; the erroneous cross-reference is not part of this assertion. -/
theorem remark_6_12 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    stableRange t = finiteStableRange t ∧
    stableRange t = (nonzeroGeneralizedSpan t : Set (Mat d)) ∧
    (stableRange t ⊆ commutant (peripheral t : Set (Mat d)) ↔
      ∀ a : ℂ, a ≠ 0 → ∀ k : ℕ, 1 ≤ k → ∀ X : Mat d,
        applyMap ((t - a • (1 : Map d))^k) X = 0 →
        X ∈ commutant (peripheral t : Set (Mat d))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
