-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreMap_eval__aeval_d46a46815112
-- name    : P2M_GroundTheory_Heights__Heights_fibreMap_eval__aeval_d46a46815112
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:42.869834+00:00
-- url     : https://prove2.me/theorems/2136e495-1904-4ff7-a898-c3865c167ff0
-- title:
--   P2 M Ground Theory Heights  Heights fibre Map eval  aeval d46a46815112: P2 M Ground Theory Heights  Heights fibre Map eval  aeval d46a46815112
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Map eval  aeval d46a46815112 construction uses the P2 M Ground Theory Heights  Heights fibre Map eval  aeval d46a46815112 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L13-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime
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

theorem P2M_GroundTheory_Heights__Heights_fibreMap_eval__aeval_d46a46815112 {σ ι : Type*} {d : ℕ} (t : σ → ℂ)
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) :
    MvPolynomial.map (eval t) (Polynomial.eval₂ (aeval y).toRingHom θ H) =
      Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) (H.map (MvPolynomial.map (eval t))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreMap_eval₂_aeval» := P2M_GroundTheory_Heights__Heights_fibreMap_eval__aeval_d46a46815112
