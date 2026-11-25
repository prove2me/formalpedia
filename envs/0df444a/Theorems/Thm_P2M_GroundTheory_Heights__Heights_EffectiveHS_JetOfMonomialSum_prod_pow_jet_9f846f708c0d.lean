-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_prod_pow_jet_9f846f708c0d
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_prod_pow_jet_9f846f708c0d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:02.938093+00:00
-- url     : https://prove2.me/theorems/fa44b138-0c87-4af9-9533-33b16ddd6e6b
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum prod pow jet 9f846f708c0d: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum prod pow jet 9f846f708c0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum prod pow jet 9f846f708c0d construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum prod pow jet 9f846f708c0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L140-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L140-L164

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_prod_pow_jet_9f846f708c0d {p : ℕ} (u : Fin p → E → ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) x)
    (hu0 : ∀ i, u i x = 0) (α : Fin p → ℕ) (w : E) (s : Finset (Fin p)) :
    AnalyticAt ℂ (fun y => ∏ i ∈ s, u i y ^ α i) x ∧
    (∀ k < ∑ i ∈ s, α i, iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, u i y ^ α i) x = 0) ∧
    iteratedFDeriv ℂ (∑ i ∈ s, α i) (fun y => ∏ i ∈ s, u i y ^ α i) x (fun _ => w) =
      (∑ i ∈ s, α i).factorial * ∏ i ∈ s, fderiv ℂ (u i) x w ^ α i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«prod_pow_jet» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_prod_pow_jet_9f846f708c0d
