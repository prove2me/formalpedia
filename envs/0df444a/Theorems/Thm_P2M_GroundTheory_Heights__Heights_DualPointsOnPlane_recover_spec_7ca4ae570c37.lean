-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_recover_spec_7ca4ae570c37
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_recover_spec_7ca4ae570c37
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:45.690803+00:00
-- url     : https://prove2.me/theorems/ff84626a-f035-412c-b296-d0950da68f06
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points On Plane recover spec 7ca4ae570c37: P2 M Ground Theory Heights  Heights Dual Points On Plane recover spec 7ca4ae570c37
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points On Plane recover spec 7ca4ae570c37 construction uses the P2 M Ground Theory Heights  Heights Dual Points On Plane recover spec 7ca4ae570c37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L36-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualPointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_recover_spec_7ca4ae570c37 (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (Z : T → ℂ) (t : T) :
    Z t = ∑ p : (K →+* ℂ) × Fin i, p.1 ((b t : Fin i → K) p.2) * dualRecover b hb Z p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOnPlane».«recover_spec» := P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_recover_spec_7ca4ae570c37
