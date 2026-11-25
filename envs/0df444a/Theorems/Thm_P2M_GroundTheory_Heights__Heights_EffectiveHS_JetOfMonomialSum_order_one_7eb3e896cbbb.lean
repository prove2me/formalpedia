-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_order_one_7eb3e896cbbb
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_order_one_7eb3e896cbbb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:18.816037+00:00
-- url     : https://prove2.me/theorems/2fec5b93-fe19-4caf-bc80-f8f8f32b5660
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum order one 7eb3e896cbbb: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum order one 7eb3e896cbbb
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum order one 7eb3e896cbbb construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum order one 7eb3e896cbbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L95-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L95-L119

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_order_one_7eb3e896cbbb {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E) :
    ∀ (a : ℕ) (g : E → ℂ), AnalyticAt ℂ g x → (∀ k < a, iteratedFDeriv ℂ k g x = 0) →
      iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
        ((a : ℂ) + 1) * iteratedFDeriv ℂ a g x (fun _ => w) * fderiv ℂ v x w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«order_one» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_order_one_7eb3e896cbbb
