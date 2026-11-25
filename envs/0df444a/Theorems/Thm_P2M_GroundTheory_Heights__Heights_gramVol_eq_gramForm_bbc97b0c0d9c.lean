-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_eq_gramForm_bbc97b0c0d9c
-- name    : P2M_GroundTheory_Heights__Heights_gramVol_eq_gramForm_bbc97b0c0d9c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:55.86669+00:00
-- url     : https://prove2.me/theorems/1a8f7084-3844-480a-958e-22165d108f0e
-- title:
--   P2 M Ground Theory Heights  Heights gram Vol eq gram Form bbc97b0c0d9c: P2 M Ground Theory Heights  Heights gram Vol eq gram Form bbc97b0c0d9c
-- statement:
--   The P2 M Ground Theory Heights  Heights gram Vol eq gram Form bbc97b0c0d9c construction uses the P2 M Ground Theory Heights  Heights gram Vol eq gram Form bbc97b0c0d9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L25-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
open scoped ENNReal

theorem P2M_GroundTheory_Heights__Heights_gramVol_eq_gramForm_bbc97b0c0d9c {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y = gramForm (v y, fderiv ℂ v y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gramVol_eq_gramForm» := P2M_GroundTheory_Heights__Heights_gramVol_eq_gramForm_bbc97b0c0d9c
