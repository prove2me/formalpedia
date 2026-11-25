-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_metric_eq_bad708170f1e
-- name    : P2M_GroundTheory_Heights__Heights_SectionInjectivity_metric_eq_bad708170f1e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:46.40021+00:00
-- url     : https://prove2.me/theorems/55d8b9a4-6764-5885-9f14-c5b45b856d57
-- title:
--   P2 M Ground Theory Heights  Heights Section Injectivity metric eq bad708170f1e: P2 M Ground Theory Heights  Heights Section Injectivity metric eq bad708170f1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Injectivity metric eq bad708170f1e construction uses the P2 M Ground Theory Heights  Heights Section Injectivity metric eq bad708170f1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L62-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L62-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_SectionInjectivity_metric_eq_bad708170f1e (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    (M.pow (q * t)).metric z = (((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric z *
        ((M.pow k).mul (HermLine.standard n).inv).metric z ^ t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionInjectivity».«metric_eq» := P2M_GroundTheory_Heights__Heights_SectionInjectivity_metric_eq_bad708170f1e
