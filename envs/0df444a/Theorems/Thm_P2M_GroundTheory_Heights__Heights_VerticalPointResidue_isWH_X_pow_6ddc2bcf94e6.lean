-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_pow_6ddc2bcf94e6
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_pow_6ddc2bcf94e6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:46.48561+00:00
-- url     : https://prove2.me/theorems/36da0f55-3eac-4b13-9b6a-66d7b633079e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X pow 6ddc2bcf94e6: P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X pow 6ddc2bcf94e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X pow 6ddc2bcf94e6 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Residue is WH X pow 6ddc2bcf94e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L43-L47

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_pow_6ddc2bcf94e6 (c : T) (n : ℕ) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ())
      (X ⟨(), c⟩ ^ n : MRing (fun _ : Unit => T)) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointResidue».«isWH_X_pow» := P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_pow_6ddc2bcf94e6
