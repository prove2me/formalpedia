-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_diag_af2eaa2d2298
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_diag_af2eaa2d2298
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:16.132284+00:00
-- url     : https://prove2.me/theorems/ed6e83b4-49b4-452e-ae84-1a43afe7a585
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fderiv diag af2eaa2d2298: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fder
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fderiv diag af2eaa2d2298 construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fderiv diag af2eaa2d2298 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L71-L74

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_diag_af2eaa2d2298 {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x (fun _ => w) =
      iteratedFDeriv ℂ (k + 1) f x (fun _ => w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«iteratedFDeriv_fderiv_diag» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_diag_af2eaa2d2298
