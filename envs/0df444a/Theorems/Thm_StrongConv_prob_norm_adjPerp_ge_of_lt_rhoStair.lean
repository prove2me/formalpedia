-- Prove2me | Theorems.Thm_StrongConv_prob_norm_adjPerp_ge_of_lt_rhoStair
-- name    : StrongConv.prob_norm_adjPerp_ge_of_lt_rhoStair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:55:36.97645+00:00
-- url     : https://prove2.me/theorems/2602e8d5-148e-448e-a3aa-0269d16d8daa
-- title:
--   Friedman's tangle lower bound — P[‖Aᴺ‖ ≥ α′] ≥ (1 − o(1))N¹⁻ᵐ for α′ < ρₘ
-- statement:
--   Let $d \ge 2$ and let $m$ satisfy $m_* < m \le d$, where $m_* = \lfloor\frac12(\sqrt{2d-1} + 1)\rfloor$. For every $\alpha' < \rho_m$ and every $\eta > 0$, for all sufficiently large $N$,
--   $$\mathbf P\big[\|A^N\| \ge \alpha'\big] \ge \frac{1 - \eta}{N^{m-1}},$$
--   where $A^N$ is the random $2d$-regular adjacency matrix restricted to $\{1_N\}^\perp$ and $\rho_m = 2m - 1 + \frac{2d-1}{2m-1}$ for such $m$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 26, the tangle lower bound cited in the proof of Theorem 3.6, which cites Friedman, J., A proof of Alon's second eigenvalue conjecture and related problems, Mem. Amer. Math. Soc. 195 (2008), no. 910, https://doi.org/10.1090/memo/0910, proof of Theorem 2.11

import Mathlib
import Definitions.Def_StrongConv

open Filter

namespace StrongConv

theorem prob_norm_adjPerp_ge_of_lt_rhoStair (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : mStar d < m)
    (hmd : m ≤ d) (α' : ℝ) (hα' : α' < rhoStair d m) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 - η) / (N : ℝ) ^ (m - 1) ≤
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => α' ≤ ‖adjPerp σ‖) := by
  sorry

end StrongConv
