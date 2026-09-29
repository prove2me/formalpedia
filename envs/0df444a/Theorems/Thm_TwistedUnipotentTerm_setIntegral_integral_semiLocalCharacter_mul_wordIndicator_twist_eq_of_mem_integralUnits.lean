-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_twist_eq_of_mem_integralUnits
-- name    : TwistedUnipotentTerm.setIntegral_integral_semiLocalCharacter_mul_wordIndicator_twist_eq_of_mem_integralUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/41c2ee8e-4a94-501f-b6db-e47863b90f83
-- title:
--   Integral twists do not change semi-local twisted unipotent integrals
-- statement:
--   Let $K \subseteq L$ be number fields, $\sigma$ a $K$-automorphism of $L$, and $\xi_L$ a homomorphism from the full group of units of the adele ring of $L$ to $\mathbb{C}^\times$. Fix a maximal ideal $v$ of $\mathcal{O}_K$, a prime $w$ of $\mathcal{O}_L$ lying under $v$, a natural number $n$, elements $r_0,\dots,r_{n-1}$ and $z$ of $\mathrm{GL}_2(L_w)$, and a Haar measure $\mu_Z$ on $(L \otimes_K K_v)^\times$ for a Borel measurable structure on that group. Write $\hat\sigma$ for the automorphism induced by $\sigma \otimes \mathrm{id}$ on $L \otimes_K K_v$ and on its units and $2 \times 2$ general linear group. Assume the semi-local character $\zeta \mapsto \prod_{w' \mid v} \xi_L(\det \mathrm{heckeGenAt}_{w'}(\zeta_{w'}))$ attached to $\xi_L$ above $v$ is $\hat\sigma$-invariant. Let $t$ be a unit lying in the image of $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$ in $L \otimes_K K_v$ whose inverse lies there too, let $k, j$ be natural numbers and $y \in L \otimes_K K_v$. Then, with $W_{k,j}(x) = \sum_{\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n} \mathbf{1}_{U}\bigl((\prod_i r_{\iota(i)} \cdot z^j)^{-1} x\bigr)$ the word indicator, where $U$ is the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ with $g$ and $g^{-1}$ both integral and the Hecke word is transported to the semi-local group, and with $\kappa$ integrated over $U$ against the Haar measure $\mathrm{semiLocalHaar}$ and $\zeta$ over $(L \otimes_K K_v)^\times$ against $\mu_Z$, $$\int_U \int \xi_v(\zeta)\, W_{k,j}\bigl(\kappa^{-1}\, n(y t^{-1})\, \mathrm{diag}(\hat\sigma(t) t^{-1}, 1)\, (\hat\sigma \zeta) I\, \hat\sigma(\kappa)\bigr)\,d\mu_Z\,d\kappa = \int_U \int \xi_v(\zeta)\, W_{k,j}\bigl(\kappa^{-1}\, \zeta I\, n(y)\bigr)\,d\mu_Z\,d\kappa,$$ where $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ and $\zeta I$ denotes the scalar matrix.
--
--   This is the invariance, under twisting by an integral unit $t$, of the semi-local $\sigma$-twisted unipotent orbital integral attached to a Hecke word above $v$: the extra diagonal and $\hat\sigma$-factors are absorbed by translation inside the integral subgroup and by right invariance of the word indicator. It is used in the twisted Bruhat analysis, namely in [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram), where twisted unipotent terms are compared along a transversal of integral units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_twist_eq_of_mem_integralUnits.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] AutomorphicForm.glBorelOf

open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.setIntegral_integral_semiLocalCharacter_mul_wordIndicator_twist_eq_of_mem_integralUnits
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (hξσ : ∀ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v
        (Units.mapEquiv (Algebra.TensorProduct.congr σ
          (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) =
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ)
    (t : (L ⊗[K] v.adicCompletion K)ˣ) (ht : t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)
    (k j : ℕ) (y : L ⊗[K] v.adicCompletion K) :
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                L ⊗[K] v.adicCompletion K)) *
              NumberField.AdelicLevel.diagOne
                (Units.mapEquiv (Algebra.TensorProduct.congr σ
                  (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
              TwistedUnipotentTerm.semiLocalCentral K L v
                (Units.mapEquiv (Algebra.TensorProduct.congr σ
                  (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
              Matrix.GeneralLinearGroup.map
                ((Algebra.TensorProduct.congr σ
                  (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ) ∂μZ
      ∂(AutomorphicForm.semiLocalHaar K L v) =
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v y) ∂μZ
      ∂(AutomorphicForm.semiLocalHaar K L v) := by sorry
