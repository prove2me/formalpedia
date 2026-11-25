-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_deg_eq_b9c28d0b278f
-- name    : P2M_GroundTheory_Heights__Heights_SectionInjectivity_deg_eq_b9c28d0b278f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:12.69488+00:00
-- url     : https://prove2.me/theorems/7cd8ce3e-0013-4186-8172-d3d11709be46
-- title:
--   P2 M Ground Theory Heights  Heights Section Injectivity deg eq b9c28d0b278f: P2 M Ground Theory Heights  Heights Section Injectivity deg eq b9c28d0b278f
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Injectivity deg eq b9c28d0b278f construction uses the P2 M Ground Theory Heights  Heights Section Injectivity deg eq b9c28d0b278f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L52-L60

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

theorem P2M_GroundTheory_Heights__Heights_SectionInjectivity_deg_eq_b9c28d0b278f (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) :
    (((M.pow (q - k)).mul (HermLine.standard n)).pow t).deg +
        t • ((M.pow k).mul (HermLine.standard n).inv).deg = (M.pow (q * t)).deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionInjectivity».«deg_eq» := P2M_GroundTheory_Heights__Heights_SectionInjectivity_deg_eq_b9c28d0b278f
