-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_secNorm_nonneg_84b67f3dd476
-- name    : P2M_GroundTheory_Heights__Heights_Inter_secNorm_nonneg_84b67f3dd476
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:03.042801+00:00
-- url     : https://prove2.me/theorems/fbd5f606-9f36-4d6b-bab8-43a10b2c3648
-- title:
--   P2 M Ground Theory Heights  Heights Inter sec Norm nonneg 84b67f3dd476: P2 M Ground Theory Heights  Heights Inter sec Norm nonneg 84b67f3dd476
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter sec Norm nonneg 84b67f3dd476 construction uses the P2 M Ground Theory Heights  Heights Inter sec Norm nonneg 84b67f3dd476 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L25-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_secNorm_nonneg_84b67f3dd476 (E : HermLine ι) (t : MRing ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 ≤ secNorm E t z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«secNorm_nonneg» := P2M_GroundTheory_Heights__Heights_Inter_secNorm_nonneg_84b67f3dd476
