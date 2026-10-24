-- Prove2me | Theorems.Thm_SecretaryAdvice_BinaryLimit_tY_limit
-- name    : SecretaryAdvice.BinaryLimit.tY_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:18.236094+00:00
-- url     : https://prove2.me/theorems/766ce5d0-c196-49f2-9c8f-670fdd8a4d81
-- title:
--   Proof of Theorem 20, p. 22 — asymptotic Y threshold
-- statement:
--   For classifier recall and specificity $p,p'\in[1/2,1]$, the $Y$ threshold normalized by the number of arrivals has the limit
--
--   $$\lim_{n\to\infty}\frac{t_Y(n,p,p')}n=\left(\frac{1-p'}p\right)^{1/p'}\exp\left(\frac{p-1}{p'}\right).$$
--
--   Together with the $N$ threshold limit, this identifies the asymptotic acceptance times. At $p'=1$ the first factor is zero, matching a $Y$ threshold of the first arrival.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 22, proof of Theorem 20, Y threshold display

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

namespace SecretaryAdvice.BinaryLimit

theorem tY_limit (p pp : ℝ) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Filter.Tendsto (fun n : ℕ => (tY n p pp : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (((1 - pp) / p) ^ (1 / pp) * Real.exp (p / pp - 1 / pp))) := by sorry

end SecretaryAdvice.BinaryLimit
