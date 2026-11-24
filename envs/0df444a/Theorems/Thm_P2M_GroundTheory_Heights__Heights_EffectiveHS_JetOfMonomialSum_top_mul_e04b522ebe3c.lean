-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_top_mul_e04b522ebe3c
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_top_mul_e04b522ebe3c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:56.300608+00:00
-- url     : https://prove2.me/theorems/10472288-2a3a-44cc-ad97-5f1dbfd4d652
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum top mul e04b522ebe3c: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum top mul e04b522ebe3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum top mul e04b522ebe3c construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum top mul e04b522ebe3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L44-L55

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_top_mul_e04b522ebe3c {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) :
    iteratedFDeriv ℂ a (fun y => f y * g y) x = g x • iteratedFDeriv ℂ a f x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«top_mul» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_top_mul_e04b522ebe3c
