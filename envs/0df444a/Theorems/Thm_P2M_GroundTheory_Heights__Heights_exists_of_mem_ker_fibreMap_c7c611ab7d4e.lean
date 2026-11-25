-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_of_mem_ker_fibreMap_c7c611ab7d4e
-- name    : P2M_GroundTheory_Heights__Heights_exists_of_mem_ker_fibreMap_c7c611ab7d4e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:59.288798+00:00
-- url     : https://prove2.me/theorems/514638bb-5fde-4d89-be2b-1167b13e64ff
-- title:
--   P2 M Ground Theory Heights  Heights exists of mem ker fibre Map c7c611ab7d4e: P2 M Ground Theory Heights  Heights exists of mem ker fibre Map c7c611ab7d4e
-- statement:
--   The P2 M Ground Theory Heights  Heights exists of mem ker fibre Map c7c611ab7d4e construction uses the P2 M Ground Theory Heights  Heights exists of mem ker fibre Map c7c611ab7d4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L63-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L63-L109

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

theorem P2M_GroundTheory_Heights__Heights_exists_of_mem_ker_fibreMap_c7c611ab7d4e {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (w : MvPolynomial ι (MvPolynomial σ ℂ))
    (hw : w ∈ RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ)) :
    ∃ (e : ℕ) (W : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      W.map (MvPolynomial.map (eval t)) = 0 ∧
        aeval y D ^ e * w - Polynomial.eval₂ (aeval y).toRingHom θ W ∈ K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_of_mem_ker_fibreMap» := P2M_GroundTheory_Heights__Heights_exists_of_mem_ker_fibreMap_c7c611ab7d4e
