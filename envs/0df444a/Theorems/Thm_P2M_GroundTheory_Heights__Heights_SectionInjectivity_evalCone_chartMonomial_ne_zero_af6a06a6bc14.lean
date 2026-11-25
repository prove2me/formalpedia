-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_evalCone_chartMonomial_ne_zero_af6a06a6bc14
-- name    : P2M_GroundTheory_Heights__Heights_SectionInjectivity_evalCone_chartMonomial_ne_zero_af6a06a6bc14
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:15.049864+00:00
-- url     : https://prove2.me/theorems/a4b428fd-fd40-48cd-9b79-1d5bb5d22563
-- title:
--   P2 M Ground Theory Heights  Heights Section Injectivity eval Cone chart Monomial ne zero af6a06a6bc14: P2 M Ground Theory Heights  Heights Section Injectivity eval Cone chart Monomial ne zero af6a06a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Injectivity eval Cone chart Monomial ne zero af6a06a6bc14 construction uses the P2 M Ground Theory Heights  Heights Section Injectivity eval Cone chart Monomial ne zero af6a06a6bc14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L22-L25

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

theorem P2M_GroundTheory_Heights__Heights_SectionInjectivity_evalCone_chartMonomial_ne_zero_af6a06a6bc14 {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionInjectivity».«evalCone_chartMonomial_ne_zero» := P2M_GroundTheory_Heights__Heights_SectionInjectivity_evalCone_chartMonomial_ne_zero_af6a06a6bc14
