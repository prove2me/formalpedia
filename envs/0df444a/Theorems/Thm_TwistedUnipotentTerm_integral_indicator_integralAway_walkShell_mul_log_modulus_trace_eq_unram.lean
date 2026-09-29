-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
-- name    : TwistedUnipotentTerm.integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/1e5291b3-5255-558e-bba1-8d69e8d4fea1
-- title:
--   Log-moments of the trace on shells at an unramified place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a height-one prime of $\mathcal O_K$ and let $w$ be an extension of $v$ to $\mathcal O_L$, that is, a height-one prime of $\mathcal O_L$ whose contraction to $\mathcal O_K$ is $v$. Assume $v$ is unramified in $L$: every height-one prime $w_2$ of $\mathcal O_L$ lying over $v$ has $\operatorname{ramificationIdx'} = 1$. Equip $L \otimes_K K_v$ (where $K_v$ is the $v$-adic completion) with a measurable space structure that is the Borel structure of its topology, and let $\nu$ be an additive Haar measure on it. Write $x \mapsto (x_{w'})_{w' \mid v}$ for the algebra isomorphism $L \otimes_K K_v \cong \prod_{w' \mid v} L_{w'}$ given by `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv`, the product being over the extensions of $v$ to $\mathcal O_L$. Then for every $h : \mathbb N \to \mathbb C$ and every $R \in \mathbb N$ with $h(r) = 0$ for all $r > R$, the function sending $x$ to the product of the indicator of $\{x : x_{w'} \in \mathcal O_{w'} \text{ for all } w' \ne w\}$ times $h\bigl((\mathrm{WithZero.log}\, v_w(x_w))_{\ge 0}\bigr)$, the argument of $h$ being the truncation to $\mathbb N$ of the integer logarithm of the $w$-adic valuation of $x_w$ (i.e. $\max(0, -\operatorname{ord}_w x_w)$), with the complex scalar $\log \mathrm{modulus}\bigl(\operatorname{Tr}_{(L \otimes_K K_v)/K_v}(x)\bigr)$, where $\mathrm{modulus}(a)$ is the scaling factor $\mathrm{distribHaarChar}$ of multiplication by $a$ on $K_v$ for $a \ne 0$ and $0$ for $a = 0$, is $\nu$-integrable, and its integral equals $$\nu\Bigl(\{x : x_{w'} \in \mathcal O_{w'} \text{ for all } w' \mid v\}\Bigr)\,\log q_v\;\Bigl(\frac{-h(0)}{q_v-1} + \sum_{r=1}^{R} h(r)\,(N_w^{\,r} - N_w^{\,r-1})\Bigl(r - \frac{1}{q_v-1} + \frac{1}{N_w-1}\Bigr)\Bigr),$$ with $q_v = \mathrm{absNorm}\, v$ and $N_w = \mathrm{absNorm}\, w$, all real quantities coerced into $\mathbb C$ and the measure of the integral box taken as a real number via `toReal`.
--
--   This is the logarithmically weighted local unipotent integral at a finite place $v$ unramified in $L$: the shells $\max(0,-\operatorname{ord}_w x_w) = r$ inside the box $\prod_{w' \ne w}\mathcal O_{w'}$ are weighted by $\log$ of the module of the trace to $K_v$, and the answer is expressed through the residue degrees of $v$ and $w$. It feeds the computation of the derivative at $1$ of the twisted local zeta factor in [`TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram`](thm.html#TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram), the identification of `modulus` with the $v$-adic norm on $K_v$ being supplied by [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∀ (h : ℕ → ℂ) (R : ℕ), (∀ r, R < r → h r = 0) →
      Integrable (fun x => {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x * ((Real.log (LanglandsTunnell.TateLocal.modulus (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) : ℝ) : ℝ) : ℂ)) ν ∧
      ∫ x, {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x * ((Real.log (LanglandsTunnell.TateLocal.modulus (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) : ℝ) : ℝ) : ℂ) ∂ν =
      ((ν {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L),
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}).toReal : ℂ) *
        ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
        (-(h 0) / ((Ideal.absNorm v.asIdeal : ℂ) - 1) +
          ∑ r ∈ Finset.Icc 1 R, h r *
            ((Ideal.absNorm w.1.asIdeal : ℂ) ^ r - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (r - 1)) *
            ((r : ℂ) - 1 / ((Ideal.absNorm v.asIdeal : ℂ) - 1) + 1 / ((Ideal.absNorm w.1.asIdeal : ℂ) - 1))) := by sorry
