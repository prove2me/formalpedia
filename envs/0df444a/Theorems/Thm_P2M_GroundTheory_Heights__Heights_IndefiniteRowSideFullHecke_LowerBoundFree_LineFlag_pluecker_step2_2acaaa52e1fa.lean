-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step2_2acaaa52e1fa
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step2_2acaaa52e1fa
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:59.007054+00:00
-- url     : https://prove2.me/theorems/be7e04c6-a6e5-5788-95ff-c60664ef099c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Line Flag pluecker step2 2acaaa52e1fa: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Boun
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Line Flag pluecker step2 2acaaa52e1fa construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Line Flag pluecker step2 2acaaa52e1fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PlueckerCoordinates/FlagLine.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PlueckerCoordinates/FlagLine.lean#L148-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step2_2acaaa52e1fa (i0 : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) (hz0 : z ⟨(), i0⟩ ≠ 0)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    IsPlueckerCoord DL.y (fun _ => i0) 0 (Pi.basisFun Ω (Fin 2)).det
      (Pi.basisFun Ω (Fin 2)) z (firstCols g 2 le_rfl) g.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LowerBoundFree».«LineFlag».«pluecker_step2» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step2_2acaaa52e1fa
