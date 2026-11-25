-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLin_eq_sum_608fd642ec52
-- name    : P2M_GroundTheory_Heights__Heights_chartLin_eq_sum_608fd642ec52
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:22.883969+00:00
-- url     : https://prove2.me/theorems/2ef73679-59d7-4605-b582-e8606b3b3f95
-- title:
--   P2 M Ground Theory Heights  Heights chart Lin eq sum 608fd642ec52: P2 M Ground Theory Heights  Heights chart Lin eq sum 608fd642ec52
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Lin eq sum 608fd642ec52 construction uses the P2 M Ground Theory Heights  Heights chart Lin eq sum 608fd642ec52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L33-L39

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

theorem P2M_GroundTheory_Heights__Heights_chartLin_eq_sum_608fd642ec52 (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartLin_eq_sum» := P2M_GroundTheory_Heights__Heights_chartLin_eq_sum_608fd642ec52
