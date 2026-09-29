-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_eq_integral_mul_setIntegral
-- name    : TwistedUnipotentTerm.setIntegral_integral_semiLocalCharacter_mul_wordIndicator_eq_integral_mul_setIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/6054fec2-f60b-5ffc-81b4-f0d99a3c8c9d
-- title:
--   Fubini exchange in the semi-local twisted unipotent integral
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $\xi_L$ be a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$, let $v$ be a nonzero prime of $\mathcal{O}_K$ and $w$ a prime of $\mathcal{O}_L$ lying under $v$ at $v$, let $n \in \mathbb{N}$, $rT \colon \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ and $z \in \mathrm{GL}_2(L_w)$, let $(L \otimes_K K_v)^\times$ carry a measurable structure which is the Borel structure of its topology, and let $\mu_Z$ be a Haar measure on $(L \otimes_K K_v)^\times$. Write $\xi_v(\zeta)$ for `semiLocalCharacter`, the finite product over the primes $w'$ of $\mathcal{O}_L$ under $v$ of $\xi_L$ evaluated at the determinant of $\mathrm{heckeGenAt}$ of the component $\mathrm{semiLocalUnitComponent}\ \zeta$ at $w'$, and assume $\xi_v$ is continuous. Let $k, j \in \mathbb{N}$ and $y \in L \otimes_K K_v$. Then the iterated integral of $\xi_v(\zeta)\, W_{k,j}\bigl(\kappa^{-1}\,(\zeta I_2)\,\begin{pmatrix}1&y\\0&1\end{pmatrix}\bigr)$, taken first over $\zeta$ against $\mu_Z$ and then over $\kappa$ in $\mathrm{semiLocalIntegralSet}$ against the Haar measure $\mathrm{semiLocalHaar}$ on $\mathrm{GL}_2(L \otimes_K K_v)$ normalised to give that set measure one, equals the integral over $\zeta$ of $\xi_v(\zeta)$ times the inner integral over $\kappa$ of the same word indicator. Here $\mathrm{semiLocalIntegralSet}$ consists of those $g$ with both $g$ and $g^{-1}$ having entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$, and $W_{k,j}$ is the sum over maps $\iota \colon \mathrm{Fin}\,k \to \mathrm{Fin}\,n$ of the indicator of that same set evaluated at $\bigl(\mathrm{semiLocalComponent}(\mathrm{localEmbed}(\prod_i rT(\iota i) \cdot z^j))\bigr)^{-1}$ times the argument.
--
--   This is the Fubini interchange of the central $\zeta$-integration with the integration over the semi-local integral set, which converts the doubly integrated expression into a $\zeta$-integral of semi-local unipotent orbital integrals. It is used in the proof of [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_eq_integral_mul_setIntegral.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] AutomorphicForm.glBorelOf

open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.setIntegral_integral_semiLocalCharacter_mul_wordIndicator_eq_integral_mul_setIntegral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (hξvc : Continuous (TwistedUnipotentTerm.semiLocalCharacter K L ξL v))
    (k j : ℕ) (y : L ⊗[K] v.adicCompletion K) :
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v y) ∂μZ
      ∂(AutomorphicForm.semiLocalHaar K L v) =
    ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
        ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v y)
          ∂(AutomorphicForm.semiLocalHaar K L v) ∂μZ := by sorry
