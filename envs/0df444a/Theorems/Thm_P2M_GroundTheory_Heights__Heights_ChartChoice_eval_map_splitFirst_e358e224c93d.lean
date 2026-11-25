-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoice_eval_map_splitFirst_e358e224c93d
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoice_eval_map_splitFirst_e358e224c93d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:18.731297+00:00
-- url     : https://prove2.me/theorems/ad998b1e-7996-49be-a87a-ae342b6492c7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice eval map split First e358e224c93d: P2 M Ground Theory Heights  Heights Chart Choice eval map split First e358e224c93d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice eval map split First e358e224c93d construction uses the P2 M Ground Theory Heights  Heights Chart Choice eval map split First e358e224c93d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L74-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartChoice
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
open GroundTheory.Heights₂.Heights.ChartChoice
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChoice_eval_map_splitFirst_e358e224c93d (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoice».«eval_map_splitFirst» := P2M_GroundTheory_Heights__Heights_ChartChoice_eval_map_splitFirst_e358e224c93d
