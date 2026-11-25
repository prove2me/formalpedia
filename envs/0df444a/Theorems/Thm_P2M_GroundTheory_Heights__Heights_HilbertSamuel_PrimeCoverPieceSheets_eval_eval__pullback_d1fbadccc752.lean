-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_eval__pullback_d1fbadccc752
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_eval__pullback_d1fbadccc752
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:22.627447+00:00
-- url     : https://prove2.me/theorems/96390bb0-b94b-483b-9018-119833511194
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval eval  pullback d1fbadccc752: P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval eval  pul
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval eval  pullback d1fbadccc752 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Cover Piece Sheets eval eval  pullback d1fbadccc752 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPrimeCoverPieceSheets.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPrimeCoverPieceSheets.lean#L39-L47

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_eval__pullback_d1fbadccc752 {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ) (G : Polynomial (MvPolynomial (Fin d) ℂ)) :
    eval x (Polynomial.eval₂ (ComplexSets.pullback A).toRingHom p G) =
      (G.map (eval (A *ᵥ x))).eval (eval x p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PrimeCoverPieceSheets».«eval_eval₂_pullback» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_eval__pullback_d1fbadccc752
