-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_linearForm_5b752603ee59
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_linearForm_5b752603ee59
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:18.68791+00:00
-- url     : https://prove2.me/theorems/f6235619-7e7c-560b-8173-b52d4d400d5d
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval linear Form 5b752603ee59: P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval linear Form
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval linear Form 5b752603ee59 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval linear Form 5b752603ee59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPrimeCoverPieceSheets.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPrimeCoverPieceSheets.lean#L49-L51

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_linearForm_5b752603ee59 {n : ℕ} (c x : Fin n → ℂ) :
    eval x (ComplexSets.sum₂ c) = ∑ j, c j * x j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PrimeCoverPieceSheets».«eval_linearForm» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_linearForm_5b752603ee59
