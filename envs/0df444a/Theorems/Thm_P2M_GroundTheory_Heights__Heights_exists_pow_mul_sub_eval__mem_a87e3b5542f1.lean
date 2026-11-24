-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_eval__mem_a87e3b5542f1
-- name    : P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_eval__mem_a87e3b5542f1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:47.486045+00:00
-- url     : https://prove2.me/theorems/b296b0d3-9439-411a-869d-829d6ef6db07
-- title:
--   P2 M Ground Theory Heights  Heights exists pow mul sub eval  mem a87e3b5542f1: P2 M Ground Theory Heights  Heights exists pow mul sub eval  mem a87e3b5542f1
-- statement:
--   The P2 M Ground Theory Heights  Heights exists pow mul sub eval  mem a87e3b5542f1 construction uses the P2 M Ground Theory Heights  Heights exists pow mul sub eval  mem a87e3b5542f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L27-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L27-L61

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

theorem P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_eval__mem_a87e3b5542f1 {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K)
    (p : MvPolynomial ι (MvPolynomial σ ℂ)) :
    ∃ (e : ℕ) (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      aeval y D ^ e * p - Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_pow_mul_sub_eval₂_mem» := P2M_GroundTheory_Heights__Heights_exists_pow_mul_sub_eval__mem_a87e3b5542f1
