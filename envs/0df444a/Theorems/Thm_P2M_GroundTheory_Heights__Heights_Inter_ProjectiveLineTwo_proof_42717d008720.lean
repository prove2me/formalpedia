-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ProjectiveLineTwo_proof_42717d008720
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ProjectiveLineTwo_proof_42717d008720
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:12.596349+00:00
-- url     : https://prove2.me/theorems/78f04234-402e-4e28-804d-dc114d231655
-- title:
--   P2 M Ground Theory Heights  Heights Inter Projective Line Two proof 42717d008720: P2 M Ground Theory Heights  Heights Inter Projective Line Two proof 42717d008720
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Projective Line Two proof 42717d008720 construction uses the P2 M Ground Theory Heights  Heights Inter Projective Line Two proof 42717d008720 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DeEqZeroOfSemiPosOff.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DeEqZeroOfSemiPosOff.lean#L55-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DeEqZeroOfSemiPosOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}

theorem P2M_GroundTheory_Heights__Heights_Inter_ProjectiveLineTwo_proof_42717d008720 (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) : SectionSpaceSymmetry := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ProjectiveLineTwo».«proof» := P2M_GroundTheory_Heights__Heights_Inter_ProjectiveLineTwo_proof_42717d008720
