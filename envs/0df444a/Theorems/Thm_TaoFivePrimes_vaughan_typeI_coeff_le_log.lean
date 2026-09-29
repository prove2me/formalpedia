-- Prove2me | Theorems.Thm_TaoFivePrimes_vaughan_typeI_coeff_le_log
-- name    : TaoFivePrimes.vaughan_typeI_coeff_le_log
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T16:21:51.635229+00:00
-- url     : https://prove2.me/theorems/832035c0-3d93-4ca6-a12b-13d5511d70ee
-- title:
--   The Vaughan Type I coefficient is bounded by $\log d$
-- statement:
--   In Vaughan's identity the second term is $\mu\mathbf 1_{\le U}*\Lambda\mathbf 1_{\le V}*\zeta$, and summing it against a test function produces the divisor coefficient
--
--   $$f(d)\;=\;\bigl(\mu\mathbf 1_{\le U}*\Lambda\mathbf 1_{\le V}\bigr)(d)\;=\;\sum_{\substack{ab=d\\ a\le U,\ b\le V}}\mu(a)\,\Lambda(b).$$
--
--   For every pair of real cutoffs $U,V$ and every natural number $d$,
--
--   $$\bigl|f(d)\bigr|\;\le\;\log d .$$
--
--   Here $\mu$ is the Möbius function, $\Lambda$ the von Mangoldt function, and $f\mathbf 1_{\le U}$ the truncation of $f$ to arguments at most $U$.
--
--   This pointwise bound is what makes the second term of Vaughan's identity a harmless Type I contribution: its coefficients are of divisor size, no larger than $\log d$ uniformly in the cutoffs, so the term can be handled by the same estimates as the first one.
--
--   **Formalization Note** At $d=0$ and $d=1$ both sides vanish, so no positivity hypothesis on $d$ is required.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 4, proof of Lemma 4.11: "where f(d) := sum_{b|d: d/U <= b <= V} mu(d/b) Lambda(b)" and "Note that |f(d)| <= sum_{b|d} Lambda(b) = log d."

import Mathlib
import Definitions.Def_TaoFivePrimes_VaughanTruncation

theorem TaoFivePrimes.vaughan_typeI_coeff_le_log (U V : ℝ) (d : ℕ) :
    |(TaoFivePrimes.truncLe U TaoFivePrimes.moebiusR *
        TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt) d| ≤ Real.log d := by sorry
