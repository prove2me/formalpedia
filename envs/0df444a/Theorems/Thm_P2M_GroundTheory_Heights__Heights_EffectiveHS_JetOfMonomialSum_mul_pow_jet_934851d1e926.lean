-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_mul_pow_jet_934851d1e926
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_mul_pow_jet_934851d1e926
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:56.873982+00:00
-- url     : https://prove2.me/theorems/105ba7e6-4d0c-4134-a503-9722ba9baebb
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum mul pow jet 934851d1e926: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum mul pow jet 934851d1e926
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum mul pow jet 934851d1e926 construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum mul pow jet 934851d1e926 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L121-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L121-L138

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_mul_pow_jet_934851d1e926 {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E)
    {g : E → ℂ} (hg : AnalyticAt ℂ g x) {c : ℕ} (hgc : ∀ k < c, iteratedFDeriv ℂ k g x = 0)
    {G : ℂ} (hG : iteratedFDeriv ℂ c g x (fun _ => w) = c.factorial * G) (m : ℕ) :
    (∀ k < c + m, iteratedFDeriv ℂ k (fun y => g y * v y ^ m) x = 0) ∧
      iteratedFDeriv ℂ (c + m) (fun y => g y * v y ^ m) x (fun _ => w) =
        (c + m).factorial * G * fderiv ℂ v x w ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«mul_pow_jet» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_mul_pow_jet_934851d1e926
