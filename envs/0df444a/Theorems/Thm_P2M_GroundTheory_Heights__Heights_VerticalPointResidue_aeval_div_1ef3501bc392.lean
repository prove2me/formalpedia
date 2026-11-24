-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_aeval_div_1ef3501bc392
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPointResidue_aeval_div_1ef3501bc392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:52.898604+00:00
-- url     : https://prove2.me/theorems/61aa8eae-151f-46f8-a1db-2adfdfb361cc
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Point Residue aeval div 1ef3501bc392: P2 M Ground Theory Heights  Heights Vertical Point Residue aeval div 1ef3501bc392
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Point Residue aeval div 1ef3501bc392 construction uses the P2 M Ground Theory Heights  Heights Vertical Point Residue aeval div 1ef3501bc392 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L103-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PVertPointResidue.lean#L103-L120

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPointResidue_aeval_div_1ef3501bc392 {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (c : T)
    (G : MRing (fun _ : Unit => T)) (n : ℕ) (hG : IsMultiHomog G (fun _ => n)) :
    aeval (fun p => y p / y ⟨(), c⟩) G = aeval y G * (y ⟨(), c⟩ ^ n)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPointResidue».«aeval_div» := P2M_GroundTheory_Heights__Heights_VerticalPointResidue_aeval_div_1ef3501bc392
