-- Prove2me | Theorems.Thm_SchoenfeldBRH_psi_bound_large_of_RH_low_count
-- name    : SchoenfeldBRH.psi_bound_large_of_RH_low_count
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T02:20:04.965098+00:00
-- url     : https://prove2.me/theorems/490c718a-675f-4fa0-a6d6-ba6f05bda5aa
-- title:
--   Schoenfeld's $\psi$ bound for $x\ge e^{13}$ from RH and a low-height zero count
-- statement:
--   Let $\psi(x)=\sum_{p^m\le x}\log p$ be Chebyshev's function and let $N(T)$ denote the number of nontrivial zeros $\rho$ of $\zeta$ with $0<\operatorname{Im}\rho\le T$, counted with multiplicity (here `DusartSmoothing.RvM.Ncount 0 T`). Assume
--
--   1. the Riemann hypothesis: every zero of $\zeta$ that is not a trivial zero $-2,-4,\dots$ and not $s=1$ has real part $\tfrac12$;
--   2. the low-height counting estimate
--   $$N(t)\le \frac{t}{2\pi}\Bigl(\log\frac{t}{2\pi}-1\Bigr)+\frac52\qquad(14\le t\le 2500).$$
--
--   Then for every $x\ge e^{13}$,
--   $$|\psi(x)-x|<\frac{\sqrt{x}\,\log^2 x}{8\pi}.$$
--
--   This is the analytic (large-$x$) half of Schoenfeld's theorem: a double-box smoothing of $\psi$ with step $h=\sqrt{x}\log x/8$, the exact explicit formula for the smoothed function, a bound for the sum over zeros via Abel summation against the Riemann–von Mangoldt main term, and a bound for the contour remainder on $\operatorname{Re}s=-\tfrac12$.
-- source:
--   L. Schoenfeld, Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II, Math. Comp. 30 (1976), 337–360, Theorem 10 (6.3) (large-x part); K. Broughan, Equivalents of the Riemann Hypothesis, Vol. 1, §4.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_CompletedZeta

theorem SchoenfeldBRH.psi_bound_large_of_RH_low_count
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2)
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 →
      (DusartSmoothing.RvM.Ncount 0 t : ℝ) ≤
        t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2)
    (x : ℝ) (hx : Real.exp 13 ≤ x) :
    |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by sorry
