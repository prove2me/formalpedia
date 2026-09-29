-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport
-- name    : TwistedUnipotentTerm.isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/4dd86dcd-a704-5360-879d-d882c43c7973
-- title:
--   Local constancy and compact support of a semi-local twisted unipotent orbital integral
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, let $\xi_L$ be a group homomorphism from the full subgroup $\top$ of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$, and let $v$ be a height-one prime of $\mathcal{O}_K$. Write $T = L\otimes_K K_v$, and equip $T^\times$ with a measurable space structure that is the Borel structure of its topology; on $\mathrm{GL}_2$ of any topological ring the Borel $\sigma$-algebra is used. Assume given a Haar measure $\mu_Z$ on $T^\times$, a function $\Phi : \mathrm{GL}_2(T)\to\mathbb{C}$ that is locally constant with compact support (this being what [`AutomorphicForm.IsSemiLocalTestFn`](def/AutomorphicForm_TwistedOrbital.html#L130) asserts), and a finite measure $\mu_T$ on $T^\times$ together with a compact set $C\subseteq T^\times$ whose complement is $\mu_T$-null. Let $\hat\sigma = \sigma\otimes\mathrm{id}$ denote the induced automorphism of $T$, of $T^\times$ and of $\mathrm{GL}_2(T)$. Then the function of $y\in T$ given by the iterated integral, over $t\in T^\times$ against $\mu_T$, over $\kappa$ in the set of $\mathrm{GL}_2(T)$-elements both of whose matrix and inverse matrix have entries in the image of $\mathcal{O}_L\otimes\mathcal{O}_{K_v}$ in $T$ against the Haar measure on $\mathrm{GL}_2(T)$ normalised by that compact open set, and over $\zeta\in T^\times$ against $\mu_Z$, of $$\chi_v(\zeta)\,\Phi\!\left(\kappa^{-1}\begin{pmatrix}1 & y t^{-1}\\ 0 & 1\end{pmatrix}\mathrm{diag}(\hat\sigma(t)t^{-1},1)\,\mathrm{scalar}(\hat\sigma(\zeta))\,\hat\sigma(\kappa)\right),$$ where $\chi_v(\zeta)$ is the finite product over the primes $w$ of $\mathcal{O}_L$ above $v$ of the values of $\xi_L$ on the determinant of the Hecke generator $\mathrm{diag}(\,\cdot\,,1)$ at the $w$-component of $\zeta$, is locally constant and has compact support.
--
--   This is the semi-local analytic input for the twisted unipotent orbital terms in the base-change comparison for $\mathrm{GL}_2$: the inner triple integral, regarded as a function of the unipotent parameter $y$, is again a locally constant compactly supported function on $L\otimes_K K_v$. It is used in the twisted Bruhat decomposition step, where such orbital functions are summed over an integral transversal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport.lean

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

theorem TwistedUnipotentTerm.isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hΦ : AutomorphicForm.IsSemiLocalTestFn K L v Φ)
    (μT : Measure (L ⊗[K] v.adicCompletion K)ˣ) [IsFiniteMeasure μT]
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) (hμTC : μT Cᶜ = 0) :
    IsLocallyConstant (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
              Φ (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                    L ⊗[K] v.adicCompletion K)) *
                  NumberField.AdelicLevel.diagOne
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
                  TwistedUnipotentTerm.semiLocalCentral K L v
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
                  Matrix.GeneralLinearGroup.map
                    ((Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ)
            ∂μZ ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) ∧
    HasCompactSupport (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
              Φ (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                    L ⊗[K] v.adicCompletion K)) *
                  NumberField.AdelicLevel.diagOne
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
                  TwistedUnipotentTerm.semiLocalCentral K L v
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
                  Matrix.GeneralLinearGroup.map
                    ((Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ)
            ∂μZ ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) := by sorry
