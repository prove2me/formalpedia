-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_step_9cbe12202740
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_step_9cbe12202740
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:28.097976+00:00
-- url     : https://prove2.me/theorems/d4db4205-67f3-406d-b228-5a6769a19c29
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum step 9cbe12202740: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum step 9cbe12202740
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum step 9cbe12202740 construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum step 9cbe12202740 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L76-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L76-L93

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_step_9cbe12202740 {g v : E → ℂ} (hg : AnalyticAt ℂ g x) (hv : AnalyticAt ℂ v x) {a : ℕ}
    (hga : ∀ k < a, iteratedFDeriv ℂ k g x = 0) (w : E) :
    iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
      fderiv ℂ v x w * iteratedFDeriv ℂ a g x (fun _ => w) +
        iteratedFDeriv ℂ a (fun y => v y * fderiv ℂ g y w) x (fun _ => w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«step» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_step_9cbe12202740
