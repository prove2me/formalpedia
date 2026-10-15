-- Prove2me | Theorems.Thm_SecretaryAdvice_BinaryLimit_tN_limit
-- name    : SecretaryAdvice.BinaryLimit.tN_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:22.493645+00:00
-- url     : https://prove2.me/theorems/e2fed329-b725-4b14-a87f-91e06de152ca
-- title:
--   Proof of Theorem 20, p. 21 — asymptotic N threshold
-- statement:
--   For classifier recall and specificity $p,p'\in[1/2,1]$, the $N$ threshold normalized by the number of arrivals has the limit
--
--   $$\lim_{n\to\infty}\frac{t_N(n,p,p')}n=\exp\left(\frac{p-1}{p'}\right).$$
--
--   This makes the paper’s logarithmic approximation of a harmonic sum into an exact limit statement. The convention $t_N=n+1$ when no $N$ coordinate is positive yields the same limit at $p=1$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 21, proof of Theorem 20, N threshold display

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

namespace SecretaryAdvice.BinaryLimit

theorem tN_limit (p pp : ℝ) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Filter.Tendsto (fun n : ℕ => (tN n p pp : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (Real.exp (p / pp - 1 / pp))) := by sorry

end SecretaryAdvice.BinaryLimit
