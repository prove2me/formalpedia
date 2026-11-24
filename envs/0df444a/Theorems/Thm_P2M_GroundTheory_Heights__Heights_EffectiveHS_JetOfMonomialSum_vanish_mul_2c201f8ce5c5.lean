-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:59.85919+00:00
-- url     : https://prove2.me/theorems/441c951a-f5a6-4485-a5d0-5c94b5093143
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish mul 2c201f8ce5c5: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish mul 2c201f8ce5c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish mul 2c201f8ce5c5 construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish mul 2c201f8ce5c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L23-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5 {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a b : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) (hgb : ∀ k < b, iteratedFDeriv ℂ k g x = 0) :
    ∀ k < a + b, iteratedFDeriv ℂ k (fun y => f y * g y) x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«vanish_mul» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5
