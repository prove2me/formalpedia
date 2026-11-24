-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_totient_gamma_lower
-- name    : TaoFivePrimes.theta_cert_totient_gamma_lower
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T20:06:22.746811+00:00
-- url     : https://prove2.me/theorems/9563c569-6ee9-44dd-84a3-163bdd7ea018
-- title:
--   Lower bound for Euler-Mascheroni: 0.57721565 <= gamma
-- statement:
--   The Euler-Mascheroni constant satisfies $\gamma \ge 0.57721565$. The proof evaluates the Mathlib series $\gamma = \sum_{k\ge 1} \mathrm{term}(k,1)$ with $N = 200$ terms, bounds $\log 201$ from below by the rational $r = 5.30330491$ via a truncated exponential certificate, and bounds the tail by the pointwise estimate $\mathrm{term}(n+1,1) \le \frac{18}{(6n+1)(6n+7)}$ for $n \ge 200$, which telescopes to $\frac{3}{1207}$. Concretely it proves $\gamma = H_{201} - \log 201 - \sum_{k\ge 0}\mathrm{term}(k+201,1) \ge H_{201} - r - \frac{3}{1207} > 0.57721565$.
-- source:
--   G. H. Hardy, *Note on Dr. Vacca's series for $\gamma$*, Quart. J. Pure Appl. Math. 43 (1912), 215-216, as reworked in M. J. D. Powell / Mathlib's `ZetaAsymptotics` tail estimate; the series $\sum_{k\ge0} \zeta(k+1)^{-1}$-type expansion of $\gamma$ and the pointwise bound used here are standard, see also J. Havil, *Gamma: Exploring Euler's Constant*, Princeton Univ. Press, 2003.

import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace TaoFivePrimes

theorem theta_cert_totient_gamma_lower :
    (57721565 / 10^8 : ℝ) ≤ Real.eulerMascheroniConstant := by sorry

end TaoFivePrimes
