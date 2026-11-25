-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_hypersurfacePresentation_of_b39368514445
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_hypersurfacePresentation_of_b39368514445
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:53.206316+00:00
-- url     : https://prove2.me/theorems/d7d55074-d053-5cab-8156-97a05ab7ad75
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation hypersurface Presentation of b39368514445: P2 M Ground Theory Heights  Heights Hypersurface Presentation hypersurface Presentation of b393
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation hypersurface Presentation of b39368514445 construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation hypersurface Presentation of b39368514445 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L200-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L200-L275

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
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
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
variable {σ ι : Type} [Finite σ] [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) [K.IsPrime]
local notation "𝔸" => MvPolynomial ι (MvPolynomial σ ℂ) ⧸ K
omit [Finite σ]
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_hypersurfacePresentation_of_b39368514445 (hKS : ∀ s : MvPolynomial σ ℂ, C s ∈ K → s = 0) :
    ∃ (d : ℕ) (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
      (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
      (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
      (u v : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      m.Monic ∧ D ≠ 0 ∧ u * m + v * Polynomial.derivative m = Polynomial.C D ∧
      (∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
        Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H) ∧
      ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«hypersurfacePresentation_of» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_hypersurfacePresentation_of_b39368514445
