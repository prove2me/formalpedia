-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_dvd_of_eval__mem_fibre_bf23f9997b48
-- name    : P2M_GroundTheory_Heights__Heights_dvd_of_eval__mem_fibre_bf23f9997b48
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:50.370582+00:00
-- url     : https://prove2.me/theorems/147af384-6891-4924-9ebe-0155dc498ace
-- title:
--   P2 M Ground Theory Heights  Heights dvd of eval  mem fibre bf23f9997b48: P2 M Ground Theory Heights  Heights dvd of eval  mem fibre bf23f9997b48
-- statement:
--   The P2 M Ground Theory Heights  Heights dvd of eval  mem fibre bf23f9997b48 construction uses the P2 M Ground Theory Heights  Heights dvd of eval  mem fibre bf23f9997b48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L111-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L111-L142

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

theorem P2M_GroundTheory_Heights__Heights_dvd_of_eval__mem_fibre_bf23f9997b48 {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
    (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hker : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
      Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H)
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (h : Polynomial (MvPolynomial (Fin d) ℂ))
    (hh : Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) h ∈ K.map (MvPolynomial.map (eval t))) :
    ∃ e : ℕ, m.map (MvPolynomial.map (eval t)) ∣
      Polynomial.C (MvPolynomial.map (eval t) D) ^ e * h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«dvd_of_eval₂_mem_fibre» := P2M_GroundTheory_Heights__Heights_dvd_of_eval__mem_fibre_bf23f9997b48
