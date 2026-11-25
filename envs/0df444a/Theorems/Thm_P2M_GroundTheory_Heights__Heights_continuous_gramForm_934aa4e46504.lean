-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_gramForm_934aa4e46504
-- name    : P2M_GroundTheory_Heights__Heights_continuous_gramForm_934aa4e46504
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:40.143495+00:00
-- url     : https://prove2.me/theorems/ee4cf4e2-420a-49b1-b3c7-70758c32fd79
-- title:
--   P2 M Ground Theory Heights  Heights continuous gram Form 934aa4e46504: P2 M Ground Theory Heights  Heights continuous gram Form 934aa4e46504
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous gram Form 934aa4e46504 construction uses the P2 M Ground Theory Heights  Heights continuous gram Form 934aa4e46504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L28-L41

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

theorem P2M_GroundTheory_Heights__Heights_continuous_gramForm_934aa4e46504 {e n : ℕ} :
    Continuous (gramForm : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_gramForm» := P2M_GroundTheory_Heights__Heights_continuous_gramForm_934aa4e46504
