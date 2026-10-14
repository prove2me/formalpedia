-- Prove2me | Theorems.Thm_TaoFivePrimes_vonMangoldt_explicit_formula
-- name    : TaoFivePrimes.vonMangoldt_explicit_formula
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-13T19:09:54.037651+00:00
-- url     : https://prove2.me/theorems/bb6e3086-4650-4f87-8f68-fdc85d66ff37
-- title:
--   Tao, Proposition 7.1 — von Mangoldt explicit formula
-- statement:
--   Let $\eta:\mathbb R\to\mathbb C$ be smooth and compactly supported, with $\eta(u)=0$ for $u<2$. The von Mangoldt explicit formula is
--
--   $$
--   \sum_{n\ge0}\Lambda(n)\eta(n)
--   =\int_{\mathbb R}\left(1-\frac1{u^3-u}\right)\eta(u)\,du
--   -\sum_{\substack{\zeta(\rho)=0\\0<\Re\rho<1}}
--    m(\rho)\int_{\mathbb R}\eta(u)u^{\rho-1}\,du.
--   $$
--
--   Here $m(\rho)$ is the analytic multiplicity of the actual zeta zero $\rho$. The zero series is unconditionally convergent. No Riemann hypothesis or finite-height placement assumption is required.
--
--   This is the full complex-cutoff statement of Tao's Proposition 7.1 and the source formula for the general positive-scale Proposition 7.2 milestone.
--
--   **Formalization Note.** The statement records the zero sum with `HasSum` over the actual critical-strip zero subtype and `analyticOrderNatAt` as multiplicity. The prime sum is finite on the support. The denominator uses the integration variable $u$, correcting the unbound $x$ in the printed equation (7.1).
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 7, Proposition 7.1, equation (7.1), https://arxiv.org/html/1201.6656v4#S7. Quoted there from Iwaniec–Kowalski, Analytic Number Theory, section 5.5. Corrects the printed unbound x to the integration variable and specifies actual zeros with analytic multiplicities and convergent summation. Captain milestone M22.

import Definitions.Def_ConnesRZ_weil_defs
open MeasureTheory

theorem TaoFivePrimes.vonMangoldt_explicit_formula (eta : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hcompact : HasCompactSupport eta) (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    HasSum (fun rho : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
      (analyticOrderNatAt riemannZeta rho.val : ℂ) *
        (∫ u : ℝ, eta u * (u : ℂ) ^ (rho.val - 1)))
      ((∫ u : ℝ, ((1 : ℂ) - 1 / (((u ^ 3 - u : ℝ) : ℂ))) * eta u) -
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * eta n)) := by sorry
