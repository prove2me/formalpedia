-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLin_self_eaf607bbd9eb
-- name    : P2M_GroundTheory_Heights__Heights_chartLin_self_eaf607bbd9eb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:22.808496+00:00
-- url     : https://prove2.me/theorems/03b307b7-84f0-41f9-8013-1cc8fd7512b6
-- title:
--   P2 M Ground Theory Heights  Heights chart Lin self eaf607bbd9eb: P2 M Ground Theory Heights  Heights chart Lin self eaf607bbd9eb
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Lin self eaf607bbd9eb construction uses the P2 M Ground Theory Heights  Heights chart Lin self eaf607bbd9eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L41-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm
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
open MvPolynomial
noncomputable section
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_chartLin_self_eaf607bbd9eb : chartLin I t e t = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartLin_self» := P2M_GroundTheory_Heights__Heights_chartLin_self_eaf607bbd9eb
