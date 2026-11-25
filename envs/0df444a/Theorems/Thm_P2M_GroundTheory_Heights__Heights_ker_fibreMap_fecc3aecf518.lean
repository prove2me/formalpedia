-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ker_fibreMap_fecc3aecf518
-- name    : P2M_GroundTheory_Heights__Heights_ker_fibreMap_fecc3aecf518
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:18.428127+00:00
-- url     : https://prove2.me/theorems/e9f1c9c0-f8c3-498b-8b9e-2c373df05200
-- title:
--   P2 M Ground Theory Heights  Heights ker fibre Map fecc3aecf518: P2 M Ground Theory Heights  Heights ker fibre Map fecc3aecf518
-- statement:
--   The P2 M Ground Theory Heights  Heights ker fibre Map fecc3aecf518 construction uses the P2 M Ground Theory Heights  Heights ker fibre Map fecc3aecf518 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericFibreTor.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericFibreTor.lean#L10-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
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

theorem P2M_GroundTheory_Heights__Heights_ker_fibreMap_fecc3aecf518 {σ ι : Type*} (t : σ → ℂ) :
    RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) =
      (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ker_fibreMap» := P2M_GroundTheory_Heights__Heights_ker_fibreMap_fecc3aecf518
