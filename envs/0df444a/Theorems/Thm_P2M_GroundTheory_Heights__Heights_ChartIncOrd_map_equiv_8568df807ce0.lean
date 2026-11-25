-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_map_equiv_8568df807ce0
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncOrd_map_equiv_8568df807ce0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:12.685079+00:00
-- url     : https://prove2.me/theorems/2ab10b24-48ee-422d-96cb-d82d6853b41c
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Ord map equiv 8568df807ce0: P2 M Ground Theory Heights  Heights Chart Inc Ord map equiv 8568df807ce0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Ord map equiv 8568df807ce0 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Ord map equiv 8568df807ce0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L181-L188

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

theorem P2M_GroundTheory_Heights__Heights_ChartIncOrd_map_equiv_8568df807ce0 (W : Ideal (MvPolynomial (Fin n) F)) :
    ((W.map (mkQ I t)).map (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t))).map
        (equiv I t e : MvPolynomial (Fin e × Fin n) (ChartQ I t) →+* MvPolynomial (Fin e) (ChartInc I t e)) =
      (W.map (chartX I t e)).map (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncOrd».«map_equiv» := P2M_GroundTheory_Heights__Heights_ChartIncOrd_map_equiv_8568df807ce0
