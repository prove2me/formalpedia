-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLoc_adjoin_eq_top_09cffd6c90ce
-- name    : P2M_GroundTheory_Heights__Heights_chartLoc_adjoin_eq_top_09cffd6c90ce
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:35.483853+00:00
-- url     : https://prove2.me/theorems/be75bdde-4747-40b4-ba9e-ba7f7ba32a19
-- title:
--   P2 M Ground Theory Heights  Heights chart Loc adjoin eq top 09cffd6c90ce: P2 M Ground Theory Heights  Heights chart Loc adjoin eq top 09cffd6c90ce
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Loc adjoin eq top 09cffd6c90ce construction uses the P2 M Ground Theory Heights  Heights chart Loc adjoin eq top 09cffd6c90ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L48-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L48-L104

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

theorem P2M_GroundTheory_Heights__Heights_chartLoc_adjoin_eq_top_09cffd6c90ce :
    Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartLoc_adjoin_eq_top» := P2M_GroundTheory_Heights__Heights_chartLoc_adjoin_eq_top_09cffd6c90ce
