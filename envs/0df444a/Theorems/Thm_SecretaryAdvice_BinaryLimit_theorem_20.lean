-- Prove2me | Theorems.Thm_SecretaryAdvice_BinaryLimit_theorem_20
-- name    : SecretaryAdvice.BinaryLimit.theorem_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:27.965416+00:00
-- url     : https://prove2.me/theorems/824c57cd-26bf-4e04-978b-3dd3d7341e4d
-- title:
--   Theorem 20, p. 20 — limit of the optimal binary-advice value
-- statement:
--   For a binary classifier with recall $p$ and specificity $p'$ in $[1/2,1]$, let $\operatorname{Opt}(n,p,p')$ be the optimal value of the section 6 primal LP for $n$ arrivals. Then
--
--   $$\lim_{n\to\infty}\operatorname{Opt}(n,p,p')=\left(\frac{1-p'}p\right)^{(1-p')/p'}\exp\left(\frac{p-1}{p'}\right).$$
--
--   This is the limiting success probability achieved by an optimal policy under the paper’s LP characterization. The finite threshold ordering and both normalized threshold limits are posed as separate milestones; the theorem’s infimum bound is posed as a companion item.
--
--   **Formalization Note** The display in Theorem 20 prints exponent $(1-p')/p$, while the last equation of its proof on page 22 gives $(1-p')/p'$. The latter is used here. `Filter.Tendsto` states the full limit, including $p'=1$, with real $0^0=1$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 20, Theorem 20, corrected limit

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

namespace SecretaryAdvice.BinaryLimit

theorem theorem_20 (p pp : ℝ) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Filter.Tendsto (fun n : ℕ => Opt n p pp) Filter.atTop (nhds (limitValue p pp)) := by sorry

end SecretaryAdvice.BinaryLimit
