-- Prove2me | Theorems.Thm_Titchmarsh_logDeriv_riemannZeta_le_log_of_riemannHypothesis
-- name    : Titchmarsh.logDeriv_riemannZeta_le_log_of_riemannHypothesis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:30:05.906463+00:00
-- url     : https://prove2.me/theorems/6d5b9907-8c01-4c08-89d1-16e8fcd491de
-- title:
--   Under RH, $\zeta'/\zeta(s)=O(\log|t|)$ for $\operatorname{Re}s\ge\tfrac12+\delta$
-- statement:
--   Assume the Riemann hypothesis, in Mathlib's form `RiemannHypothesis`. Fix $\delta>0$. Then there is a constant $C=C(\delta)$ such that
--
--   $$\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\le C\log|t|\qquad\text{whenever}\quad \tfrac12+\delta\le\sigma\le2,\ \ |t|\ge2 .$$
--
--   Under RH the logarithmic derivative of $\zeta$ therefore grows at most logarithmically in every closed half-strip strictly to the right of the critical line. Titchmarsh–Heath-Brown prove the sharper bound $\zeta'/\zeta(s)=O\big((\log t)^{2-2\sigma+\varepsilon}\big)$ under RH (§14.5), and the stated bound is weaker. It follows from the Borel–Carathéodory control of $\log\zeta$ on discs of radius $\tfrac32-O(\delta)$ centred at $2+it$ (§14.2), combined with Cauchy's estimate for the derivative. It is a standard input to conditional explicit formulas, for instance for $\psi(x)$ and $M(x)$.
--
--   **Formalization Note.** `deriv riemannZeta s / riemannZeta s` is the logarithmic derivative. On the region considered, $s\neq1$ and, under the hypothesis, $\zeta(s)\neq0$, so this is the genuine $\zeta'/\zeta$. The constant depends only on $\delta$. The restriction $|t|\ge2$ keeps $\log|t|$ bounded below by $\log2>0$ and keeps $s$ away from the pole.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, §14.2 (Theorem 14.2 and the Borel–Carathéodory argument for log ζ under RH) and §14.5 (bounds for ζ'/ζ under RH); the stated O(log t) bound is a weak form of those results. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf

import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Titchmarsh

theorem logDeriv_riemannZeta_le_log_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |s.im| := by sorry

end Titchmarsh
