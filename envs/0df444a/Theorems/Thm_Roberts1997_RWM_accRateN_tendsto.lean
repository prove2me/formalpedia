-- Prove2me | Theorems.Thm_Roberts1997_RWM_accRateN_tendsto
-- name    : Roberts1997.RWM.accRateN_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:49:40.541848+00:00
-- url     : https://prove2.me/theorems/d6eec03b-0600-4b34-b94c-802b3a52e7ed
-- title:
--   Corollary 1.2 (i) — the average acceptance rate a_n(l) converges to a(l) = 2Φ(−l√I/2)
-- statement:
--   Let $f$ satisfy the standing hypotheses and $l>0$. With $a_n(l)=\int\!\!\int\pi_n(x)\,\alpha(x,y)\,q_n(x,y)\,dx\,dy$ the average acceptance rate of the random walk Metropolis algorithm in $n$ dimensions,
--
--   $$ \lim_{n\to\infty}a_n(l)=a(l)=2\,\Phi\Big(-\frac{l\sqrt I}{2}\Big). $$
--
--   Together with Corollary 1.2 (ii) this gives the practical rule of the paper: tune the proposal variance so that the average acceptance rate is about $0.23$.
--
--   **Formalization Note** $q_n(x,y)\,dy$ is written as integration against the proposal measure $N(x,\sigma_n^2I_n)$. The inner integrand lies in $[0,1]$ and is jointly measurable, so both integrals are genuine.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 113, Corollary 1.2 (i); definitions of a_n(l) and a(l) on p. 112

import Definitions.Def_Roberts1997_RWM_IsRegularTarget
import Definitions.Def_Roberts1997_RWM_Target
import Definitions.Def_Roberts1997_RWM_Speed

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Roberts1997.RWM

/-- Corollary 1.2 (i) (p. 113). `lim_{n→∞} a_n(l) = a(l) = 2Φ(-l√I/2)`. -/
theorem accRateN_tendsto (f : ℝ → ℝ) (hf : IsRegularTarget f) (l : ℝ) (hl : 0 < l) :
    Tendsto (fun n : ℕ => accRateN f n l) atTop (𝓝 (accRate f l)) := by sorry

end Roberts1997.RWM
