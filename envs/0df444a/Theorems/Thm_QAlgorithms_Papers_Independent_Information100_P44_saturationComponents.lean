-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_saturationComponents
-- name    : QAlgorithms.Papers.Independent.Information100.P44.saturationComponents
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:35:27.626473+00:00
-- url     : https://prove2.me/theorems/cd9cf210-fe98-4168-bc4a-2086cf993d57
-- title:
--   Corollary 3: connected components collapse to complex rays
-- statement:
--   Choose elementary coherence-transfer bounds of a finite-bath thermal operation, each with matching input and output energy gaps. Form the undirected graph whose vertices are nonzero shell vectors, labelled by transitions $(r,i)$, and whose edges are the selected pairs. If all selected bounds are saturated, then for each connected component $C$ there is a nonzero vector $v$ such that
--   $$\forall (r,i)\in C,\qquad w_{r|i}\in\mathbb C v.$$
--   The graph concerns complex collinearity only. The common-phase condition for sums remains a separate requirement.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 11, Corollary 3: connected components collapse to complex rays

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.11, Corollary 3: every connected component of nonzero vectors lies in one complex ray. -/
theorem saturationComponents {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) (edges : TransferEdges d)
    (hgaps : ∀ e ∈ edges, E e.1.2 - E e.2.2 = E e.1.1 - E e.2.1)
    (hsat : JointElementary (thermalApply D) edges)
    (u : {a : Fin d × Fin d // shellVector D a.1 a.2 ≠ 0}) :
    ∃ v : EuclideanSpace ℂ (Fin b × Fin b), v ≠ 0 ∧
      ∀ z : {a : Fin d × Fin d // shellVector D a.1 a.2 ≠ 0},
        Relation.ReflTransGen (saturationAdj D edges) u z →
        ∃ c : ℂ, shellVector D z.val.1 z.val.2 = c • v := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
