-- Prove2me | Theorems.Thm_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
-- name    : UnramifiedWhittaker.integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/80baed1f-6878-5b9e-8188-7aef54279ce5
-- title:
--   Entirety of a bounded, pinched S-part zeta integral
-- statement:
--   Let $F$ be a number field and $S$ a finite set of nonzero primes of $\mathcal{O}_F$, and write $\nu_S$ for [`NumberField.Idele.sPartMeasure F S`](def/NumberField_IdeleProductMeasure.html#L458), the pushforward along the monoid map `partAt F S` induced on ideles of the $S$-part map, of the Haar measure `idelicHaar F` on $\mathbb{A}_F^\times$ restricted to the subgroup of unit ideles $\delta$ with $\delta_v$ and $(\delta^{-1})_v$ integral at every finite $v \notin S$. Let $Wg\colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function, $\chi\colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ a group homomorphism, $\mu\colon \mathbb{A}_F^\times \to \mathbb{R}$ a function, and $\Omega, K \subseteq \mathbb{A}_F^\times$ sets measurable for the Borel $\sigma$-algebra [`NumberField.Idele.ideleBorel F`](def/NumberField_IdeleProductMeasure.html#L384), with $\nu_S(\Omega^{c}) = 0$ and $\nu_S(K) < \infty$. Let $M_0, M_1, X, r, R$ be real with $r > 0$. Assume that for each $s \in \mathbb{C}$ the function $a \mapsto \mu(a)\,Z(s,a)$ is Borel measurable, where $Z(s,a) = Wg(\mathrm{diag}(a,1))\,\chi(a)\,\lVert a\rVert^{\,s-1}$ is `zetaIntegrand`, $\mathrm{diag}(a,1)$ being `diagOne a` and $\lVert a\rVert =$ `ideleNorm F a` the modulus of $a$ acting on $\mathbb{A}_F$; that $|\mu(a)| \le M_0$ for all $a$; that $\mu(a) = 0$ for $a \in \Omega$ with $a \notin K$; and that for every $a \in K$ one has $\lVert Wg(\mathrm{diag}(a,1))\rVert \le M_1$, $\lVert\chi(a)\rVert \le X$ and $r \le \lVert a\rVert \le R$. Then $a \mapsto \mu(a)\,Z(s,a)$ is $\nu_S$-integrable for every $s \in \mathbb{C}$, and $s \mapsto \int \mu(a)\,Z(s,a)\,d\nu_S(a)$ is complex differentiable on all of $\mathbb{C}$.
--
--   This is the Tate-style convergence-and-holomorphy step for a zeta integral over the $S$-part of the idele class torus, in the form needed when a bounded multiplier $\mu$ confines the integrand to a set of finite measure on which the Whittaker function, the character and the idelic norm are all pinched between explicit bounds: the integral then converges absolutely for every $s$ and defines an entire function. It is used in the construction of a nonvanishing entire zeta integral attached to a unipotent average of a right convolution, [`AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero`](thm.html#AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero), and relies only on the continuity of the idelic norm [`NumberField.TateGlobal.continuous_ideleNorm`](thm.html#NumberField.TateGlobal.continuous_ideleNorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem UnramifiedWhittaker.integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Wg : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (μ : (AdeleRing (𝓞 F) F)ˣ → ℝ)
    (Ω K : Set (AdeleRing (𝓞 F) F)ˣ) (hΩm : MeasurableSet[NumberField.Idele.ideleBorel F] Ω) (hKm : MeasurableSet[NumberField.Idele.ideleBorel F] K)
    (hΩ : NumberField.Idele.sPartMeasure F S Ωᶜ = 0) (hK : NumberField.Idele.sPartMeasure F S K < ⊤)
    (M₀ M₁ X r R : ℝ) (hr : 0 < r)
    (hmeas : ∀ s : ℂ, Measurable[NumberField.Idele.ideleBorel F] fun a => (μ a : ℂ) * zetaIntegrand Wg χ s a)
    (hμ : ∀ a, |μ a| ≤ M₀)
    (hsupp : ∀ a ∈ Ω, a ∉ K → μ a = 0)
    (hKb : ∀ a ∈ K, ‖Wg (diagOne a)‖ ≤ M₁ ∧ ‖((χ a : ℂˣ) : ℂ)‖ ≤ X ∧ r ≤ ideleNorm F a ∧ ideleNorm F a ≤ R) :
    (∀ s : ℂ, Integrable (fun a => (μ a : ℂ) * zetaIntegrand Wg χ s a) (NumberField.Idele.sPartMeasure F S)) ∧
    Differentiable ℂ (fun s : ℂ => ∫ a, (μ a : ℂ) * zetaIntegrand Wg χ s a ∂(NumberField.Idele.sPartMeasure F S)) := by sorry
