-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_cross_7af2443d38e3
-- name    : P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_cross_7af2443d38e3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:39.93135+00:00
-- url     : https://prove2.me/theorems/ae5315e3-1e6a-415c-9e59-0db23efa6871
-- title:
--   P2 M Ground Theory Heights  Heights Section Injectivity chart Form cross 7af2443d38e3: P2 M Ground Theory Heights  Heights Section Injectivity chart Form cross 7af2443d38e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Injectivity chart Form cross 7af2443d38e3 construction uses the P2 M Ground Theory Heights  Heights Section Injectivity chart Form cross 7af2443d38e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L27-L38

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

theorem P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_cross_7af2443d38e3 {P : ArithVariety n} {num den : MvPolynomial (Coord n) ℤ}
    (hden : den ∉ P.ideal) {c : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ}
    {f f' : MvPolynomial (Coord n) ℤ} (h : den * f - num * chartMonomial c d ∈ P.ideal)
    (h' : den * f' - num * chartMonomial c d' ∈ P.ideal) :
    f * chartMonomial c d' - f' * chartMonomial c d ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionInjectivity».«chartForm_cross» := P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_cross_7af2443d38e3
