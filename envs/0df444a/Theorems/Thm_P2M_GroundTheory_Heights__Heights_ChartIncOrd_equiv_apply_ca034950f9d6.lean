-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_equiv_apply_ca034950f9d6
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncOrd_equiv_apply_ca034950f9d6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:25.63442+00:00
-- url     : https://prove2.me/theorems/2e27edc8-74b7-47ad-bff5-c28f3673867d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Ord equiv apply ca034950f9d6: P2 M Ground Theory Heights  Heights Chart Inc Ord equiv apply ca034950f9d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Ord equiv apply ca034950f9d6 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Ord equiv apply ca034950f9d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L179-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L179-L179

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
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
open GroundTheory.Heights₂.Heights.ChartIncOrd
variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)

theorem P2M_GroundTheory_Heights__Heights_ChartIncOrd_equiv_apply_ca034950f9d6 (y : MvPolynomial (Fin e × Fin n) (ChartQ I t)) : equiv I t e y = fwd I t e y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncOrd».«equiv_apply» := P2M_GroundTheory_Heights__Heights_ChartIncOrd_equiv_apply_ca034950f9d6
