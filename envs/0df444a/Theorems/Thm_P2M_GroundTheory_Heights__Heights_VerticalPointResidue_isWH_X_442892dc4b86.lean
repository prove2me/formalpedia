-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_442892dc4b86
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_442892dc4b86
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:34.226668+00:00
-- url     : https://prove2.me/theorems/36230f25-6923-4502-b5fb-04792e6feedd
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X 442892dc4b86: P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X 442892dc4b86
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X 442892dc4b86 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X 442892dc4b86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L37-L40

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
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_442892dc4b86 (c : T) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ())
      (X ⟨(), c⟩ : MRing (fun _ : Unit => T)) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointResidue».«isWH_X» := P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_442892dc4b86
