-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_lemma_3_11
-- name    : SingleMachineSched.AlphaJSched.lemma_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:20:51.444349+00:00
-- url     : https://prove2.me/theorems/04c5e4c3-35e8-4399-9d89-7b512b0c32da
-- title:
--   Lemma 3.11 — the two properties of the density $g$
-- statement:
--   Let $\gamma$ satisfy $0<\gamma<1$ and $\gamma+\ln(2-\gamma)=e^{-\gamma}\bigl((2-\gamma)e^{\gamma}-1\bigr)$, let $\delta=\gamma+\ln(2-\gamma)$, $c=1+e^{-\gamma}/\delta$, and let
--   $$g(\alpha)=\begin{cases}(c-1)e^{\alpha}&\text{if }0<\alpha\le\delta,\\0&\text{otherwise.}\end{cases}$$
--   Write $E_g[\alpha]=\int_0^1\alpha\,g(\alpha)\,d\alpha$. Then $g$ is a density function on $(0,1]$, that is, $g\ge0$ and $\int_0^1 g(\alpha)\,d\alpha=1$, and
--
--   1. $\displaystyle\int_0^\eta g(\alpha)(1+\alpha-\eta)\,d\alpha\ \le\ (c-1)\,\eta$ for all $\eta\in[0,1]$;
--   2. $\displaystyle\bigl(1+E_g[\alpha]\bigr)\int_\mu^1 g(\alpha)\,d\alpha\ \le\ c\,(1-\mu)$ for all $\mu\in[0,1]$.
--
--   Property (i) bounds the expected delay caused by jobs in $N_1$ and property (ii) the delay caused by jobs in $N_2$, in the right-hand side of (3.11). The lemma is a statement in real analysis about one explicit function.
--
--   **Formalization Note.** $E_g[\alpha]$ is the integral against $g$, not the expectation of a random variable. The integrals in (i) and (ii) are oriented interval integrals, which agree with the paper's for $\eta,\mu\in[0,1]$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 185, Lemma 3.11

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_DensityG

namespace SingleMachineSched.AlphaJSched

/-- Lemma 3.11: for the root `γ ∈ (0, 1)` of `γ + ln(2 − γ) = e^{−γ}((2 − γ)e^γ − 1)`, the
function `g` of Theorem 3.9 is a probability density on `(0, 1]`, and
(i) `∫_0^η g(α)(1 + α − η) dα ≤ (c − 1) η` for all `η ∈ [0, 1]`;
(ii) `(1 + E_g[α]) ∫_μ^1 g(α) dα ≤ c (1 − μ)` for all `μ ∈ [0, 1]`. -/
theorem lemma_3_11 (γ : ℝ)
    (hγ : 0 < γ ∧ γ < 1 ∧
      γ + Real.log (2 - γ) = Real.exp (-γ) * ((2 - γ) * Real.exp γ - 1)) :
    ((∀ a, 0 ≤ gDens γ a) ∧ ∫ a in Set.Ioc (0 : ℝ) 1, gDens γ a = 1) ∧
      (∀ η ∈ Set.Icc (0 : ℝ) 1,
        ∫ a in (0 : ℝ)..η, gDens γ a * (1 + a - η) ≤ (cConst γ - 1) * η) ∧
      (∀ μ ∈ Set.Icc (0 : ℝ) 1,
        (1 + Eg γ) * ∫ a in μ..1, gDens γ a ≤ cConst γ * (1 - μ)) := by sorry

end SingleMachineSched.AlphaJSched
