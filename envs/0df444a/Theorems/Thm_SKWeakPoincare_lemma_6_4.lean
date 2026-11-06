-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_6_4
-- name    : SKWeakPoincare.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:39:59.936194+00:00
-- url     : https://prove2.me/theorems/6e941232-ca40-4405-98d0-9d85828a6f4d
-- title:
--   Lemma 6.4 — averaged terminal posterior variance $\le Cn^7\mathcal E+\frac14e^{-cn}\operatorname{osc}^2$ on $\Omega_n^{\mathrm{end}}$
-- statement:
--   Fix $0<\beta_0<\beta_1<1$. There are constants $T_0,C,c,N>0$, depending only on $(\beta_0,\beta_1)$, such that for every $n\ge N$ there is an event $\Omega_n^{\mathrm{end}}$ of $P_{0,n}$-probability at least $1-Ce^{-cn}$ with the following property. For every $A\in\Omega_n^{\mathrm{end}}$, every $\beta\in[\beta_0,\beta_1]$ and every $f:\{\pm1\}^n\to\mathbb R$, with $X\sim\mu_{\beta,A}$, $(B_t)$ an independent standard Brownian motion and $Y_t=tX+B_t$,
--   $$
--   E_{X\sim\mu_{\beta,A},B}\big[\mathrm{Var}_{\mu_{A,Y_{T_0}}}[f]\big]\le Cn^7\,\mathcal E_{\mu_{\beta,A}}(f,f)+\tfrac14e^{-cn}\operatorname{osc}(f)^2,
--   $$
--   where $\mu_{A,y}$ is the Gibbs distribution at inverse temperature $\beta$ with external field $y$.
--
--   This supplies the averaged terminal posterior-variance hypothesis of Lemma 6.1, with $a_n=Cn^7$ and $\delta_n=e^{-cn}/4$.
--
--   **Formalization Note** The expectation is a finite sum over $X$ against $\mu_{\beta,A}=$ `gibbs (β • W)` and an integral over $g\sim N(0,I_n)$, with $B_{T_0}=\sqrt{T_0}\,g$. The event is a measurable set of disorders.
--
--   Differences from the source:
--   - encoding: E over X ∼ μ_{β,A} and an independent Brownian motion of a function of Y_{T₀} = T₀X + B_{T₀} → Σₓ μ_{β,A}(x) ∫ Var_{μ_{A, T₀x + √T₀ g}}[f] d N(0,I_n)(g); reason: the integrand depends on B only through B_{T₀} ∼ √T₀ g
--   - encoding: an event of P_{0,n}-probability at least 1 − C exp(−cn) → a measurable G with disorderLaw n G ≥ 1 − C e^{−cn}; reason: P_{0,n} is disorderLaw n
--   - encoding: 𝓔_{μ_{β,A}}(f,f), osc(f), μ_{A,y} → glauberDirichlet (gibbs (β • W)) f, hMax f − hMin f, tilt (gibbs (β • W)) y; reason: the paper's definitions (pp.2, 14, 37)
--   - encoding: N > 0 → N : ℕ with 0 < N; reason: n is a natural number
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 6.4, p.41 (proof Appendix D)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_gibbsOf
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_plantedTilted

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory

namespace SKWeakPoincare

/-- **Lemma 6.4 (averaged terminal posterior variance).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 6.4, p. 41 (proof in Appendix D).

Fix `0 < β₀ < β₁ < 1`. There are `T₀, C, c, N > 0`, depending only on `(β₀, β₁)`, such that for every
`n ≥ N` there is an event `Ω_n^end` of `P_{0,n}`-probability at least `1 − C exp(−cn)` with: for every
`A ∈ Ω_n^end`, every `β ∈ [β₀, β₁]`, `X ∼ μ_{β,A}`, an independent standard Brownian motion `B` and
`Y_t = tX + B_t`, and every `f : {±1}^n → ℝ`,
`E_{X∼μ_{β,A}, B}[Var_{μ_{A,Y_{T₀}}}[f]] ≤ C n⁷ 𝓔_{μ_{β,A}}(f, f) + ¼ exp(−cn) osc(f)²`,
where `μ_{A,y}` is the Gibbs distribution at inverse temperature `β` and external field `y`.

**Formalization Note.** The expectation depends only on the law `N(0, T₀ I_n)` of `B_{T₀}`, written as
`√T₀ g` with `g ∼ gaussVecLaw n`; the expectation over `X` is the finite sum against `gibbs (β • W)`.
`μ_{A,y} = tilt (gibbs (β • W)) y`; `𝓔` is `glauberDirichlet`, `osc(f) = hMax f − hMin f`. The event is
a measurable set `G` of disorders with `disorderLaw n G ≥ 1 − C e^{−cn}`. -/
theorem lemma_6_4 (β₀ β₁ : ℝ) (h0 : 0 < β₀) (h01 : β₀ < β₁) (h1 : β₁ < 1) :
    ∃ (T₀ C c : ℝ) (N : ℕ), 0 < T₀ ∧ 0 < C ∧ 0 < c ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ G : Set (Disorder n), MeasurableSet G ∧
        ENNReal.ofReal (1 - C * Real.exp (-(c * n))) ≤ disorderLaw n G ∧
        ∀ W ∈ G, ∀ β ∈ Set.Icc β₀ β₁, ∀ f : Spin n → ℝ,
          ∑ x, gibbs (β • W) x *
              ∫ g, lawVar (tilt (gibbs (β • W)) (T₀ • spinVec x + Real.sqrt T₀ • g)) f
                ∂(gaussVecLaw n) ≤
            C * (n : ℝ) ^ 7 * glauberDirichlet (gibbs (β • W)) f +
              (1 / 4) * Real.exp (-(c * n)) * (hMax f - hMin f) ^ 2 := by sorry

end SKWeakPoincare
