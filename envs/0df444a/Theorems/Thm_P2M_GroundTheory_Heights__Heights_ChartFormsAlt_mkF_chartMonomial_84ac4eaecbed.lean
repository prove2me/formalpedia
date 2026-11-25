-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_mkF_chartMonomial_84ac4eaecbed
-- name    : P2M_GroundTheory_Heights__Heights_ChartFormsAlt_mkF_chartMonomial_84ac4eaecbed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:23:24.995871+00:00
-- url     : https://prove2.me/theorems/8a491d9c-130a-4271-a4af-e7a5df44448e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Forms Alt mk F chart Monomial 84ac4eaecbed: P2 M Ground Theory Heights  Heights Chart Forms Alt mk F chart Monomial 84ac4eaecbed
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Forms Alt mk F chart Monomial 84ac4eaecbed construction uses the P2 M Ground Theory Heights  Heights Chart Forms Alt mk F chart Monomial 84ac4eaecbed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L35-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing
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
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartFormsAlt_mkF_chartMonomial_84ac4eaecbed (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (e : ι → ℕ) :
    P.mkF (chartMonomial c e) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFormsAlt».«mkF_chartMonomial» := P2M_GroundTheory_Heights__Heights_ChartFormsAlt_mkF_chartMonomial_84ac4eaecbed
