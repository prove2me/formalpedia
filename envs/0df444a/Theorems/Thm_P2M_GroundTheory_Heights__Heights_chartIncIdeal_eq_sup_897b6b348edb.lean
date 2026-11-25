-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartIncIdeal_eq_sup_897b6b348edb
-- name    : P2M_GroundTheory_Heights__Heights_chartIncIdeal_eq_sup_897b6b348edb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:48.373191+00:00
-- url     : https://prove2.me/theorems/40c3cb0c-4306-4aaf-a303-dbb94cad7195
-- title:
--   P2 M Ground Theory Heights  Heights chart Inc Ideal eq sup 897b6b348edb: P2 M Ground Theory Heights  Heights chart Inc Ideal eq sup 897b6b348edb
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Inc Ideal eq sup 897b6b348edb construction uses the P2 M Ground Theory Heights  Heights chart Inc Ideal eq sup 897b6b348edb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L50-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
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

theorem P2M_GroundTheory_Heights__Heights_chartIncIdeal_eq_sup_897b6b348edb {F : Type} [Field F] {n : ℕ} {I W : Ideal (MvPolynomial (Fin n) F)}
    (t : Fin n → F) (e : ℕ) (h : I ≤ W) :
    chartIncIdeal W t e = W.map (rename Sum.inl) ⊔ chartIncIdeal I t e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartIncIdeal_eq_sup» := P2M_GroundTheory_Heights__Heights_chartIncIdeal_eq_sup_897b6b348edb
