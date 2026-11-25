-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_dvd_of_dvd_map_eval_139eb59d4b54
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_dvd_of_dvd_map_eval_139eb59d4b54
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:45.533674+00:00
-- url     : https://prove2.me/theorems/59d13a3d-d7ae-50f6-9a3f-1aa3b3987a7c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets dvd of dvd map eval 139eb59d4b54: P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets dvd of dvd map
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets dvd of dvd map eval 139eb59d4b54 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets dvd of dvd map eval 139eb59d4b54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPrimeCoverPieceSheets.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPrimeCoverPieceSheets.lean#L19-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPrimeCoverPieceSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPrimeCoverPieceSheets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_dvd_of_dvd_map_eval_139eb59d4b54 {d : ℕ} {G m : Polynomial (MvPolynomial (Fin d) ℂ)} (hG : G.Monic)
    {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    (h : ∀ y : Fin d → ℂ, eval y Q ≠ 0 → G.map (eval y) ∣ m.map (eval y)) : G ∣ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PrimeCoverPieceSheets».«dvd_of_dvd_map_eval» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_dvd_of_dvd_map_eval_139eb59d4b54
