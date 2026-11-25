-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_ae_eval_ne_zero_9e323230ff5d
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_ae_eval_ne_zero_9e323230ff5d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:11:40.726809+00:00
-- url     : https://prove2.me/theorems/3d8b6067-95dd-521c-823c-20f1795e8fc7
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise ae eval ne zero 9e323230ff5d: P2 M Ground Theory Heights  Heights Lelong Regularise ae eval ne zero 9e323230ff5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise ae eval ne zero 9e323230ff5d construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise ae eval ne zero 9e323230ff5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L122-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_ae_eval_ne_zero_9e323230ff5d {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : ι → ℂ, MvPolynomial.eval w g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«ae_eval_ne_zero» := P2M_GroundTheory_Heights__Heights_LelongRegularise_ae_eval_ne_zero_9e323230ff5d
