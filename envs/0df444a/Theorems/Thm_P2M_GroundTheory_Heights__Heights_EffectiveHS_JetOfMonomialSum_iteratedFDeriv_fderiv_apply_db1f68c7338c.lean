-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_apply_db1f68c7338c
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_apply_db1f68c7338c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:13.14866+00:00
-- url     : https://prove2.me/theorems/dda3679d-67a7-403b-bd25-cbb8232cb878
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fderiv apply db1f68c7338c: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fde
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fderiv apply db1f68c7338c construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum iterated FDeriv fderiv apply db1f68c7338c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L57-L64

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_apply_db1f68c7338c {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ)
    (m : Fin k → E) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x m =
      iteratedFDeriv ℂ (k + 1) f x (Fin.snoc m w : Fin (k + 1) → E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«iteratedFDeriv_fderiv_apply» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_apply_db1f68c7338c
