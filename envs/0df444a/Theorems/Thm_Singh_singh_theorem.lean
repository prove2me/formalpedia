-- Prove2me | Theorems.Thm_Singh_singh_theorem
-- name    : Singh.singh_theorem
-- status  : Proved
-- author  : @Hix_Lab
-- created : 2026-11-04T06:03:40.554631+00:00
-- url     : https://prove2.me/theorems/00f6e1b1-9f0b-4c88-93e7-19d720bff64d
-- title:
--   Singh Theorem: $V_N(s)/s^2 \to \frac{\pi^2}{15}\left(1-\frac{4}{N^2}\right)$
-- statement:
--   For every integer $N \ge 2$,
--   $$\lim_{s \to 0^+} \frac{V_N(s)}{s^2} = c_N, \qquad c_N = \frac{\pi^2}{15}\left(1 - \frac{4}{N^2}\right),$$
--   where $V_N(s)$ (`cueV N s`) is the conditional variance of $X = \log|\Lambda'(\theta_1)| - \log|\Lambda'(\theta_2)|$ for two adjacent eigenangles of a Haar unitary $U \in U(N)$ at normalized gap $s = N(\theta_2-\theta_1)/(2\pi)$. Concretely, with $n = N-2$ and $\delta = 2\pi s/N$, $V_N(s)$ is the variance of $X_\delta(\theta) = \sum_{k=1}^{n} \left(\log\sin\frac{\theta_k+\delta/2}{2} - \log\sin\frac{\theta_k-\delta/2}{2}\right)$ under the probability density on $(\delta/2, 2\pi-\delta/2)^n$ proportional to $\prod_{a<b}\sin^2\frac{\theta_a-\theta_b}{2}\prod_k \sin^2\frac{\theta_k-\delta/2}{2}\sin^2\frac{\theta_k+\delta/2}{2}$.
-- source:
--   J. Singh, https://github.com/jjsingh88/singh-constant (commit 792d985)

import Mathlib
import Definitions.Def_Singh

open MeasureTheory Filter Topology

namespace Singh

theorem singh_theorem {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun s => cueV N s / s ^ 2) (𝓝[>] 0)
      (𝓝 (Real.pi ^ 2 / 15 * (1 - 4 / (N : ℝ) ^ 2))) := by sorry

end Singh
