-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:12.328065+00:00
-- url     : https://prove2.me/theorems/62c74772-4033-4704-86db-3acc5df8eef9
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Residue is Multi Homog iff fb8717c574c6: P2 M Ground Theory Heights  Heights Vertical Point Residue is Multi Homog iff fb8717c574c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Residue is Multi Homog iff fb8717c574c6 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Residue is Multi Homog iff fb8717c574c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L18-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointResidue
variable {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6 {g : MRing (fun _ : Unit => T)} {n : ℕ} :
    IsMultiHomog g (fun _ => n) ↔
      IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) g n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointResidue».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6
