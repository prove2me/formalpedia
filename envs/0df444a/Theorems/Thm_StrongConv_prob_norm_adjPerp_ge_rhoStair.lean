-- Prove2me | Theorems.Thm_StrongConv_prob_norm_adjPerp_ge_rhoStair
-- name    : StrongConv.prob_norm_adjPerp_ge_rhoStair
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T22:56:09.698091+00:00
-- url     : https://prove2.me/theorems/b0ed8976-de8a-4003-b567-6ba3daad2555
-- title:
--   Theorem 3.6 — the staircase theorem
-- statement:
--   Let $d \ge 2$, and let $\rho_m = 2\sqrt{2d-1}$ if $2m - 1 \le \sqrt{2d-1}$ and $\rho_m = 2m - 1 + \frac{2d-1}{2m-1}$ otherwise, with $m_* = \lfloor\frac12(\sqrt{2d-1}+1)\rfloor$. There is a constant $C_d$, depending only on $d$, such that for every $m$ with $m_* \le m \le d - 1$ and every $0 < \varepsilon < \rho_{m+1} - \rho_m$:
--   1. $\mathbf P\big[\|A^N\| \ge \rho_m + \varepsilon\big] \le \frac{C_d}{N^m\varepsilon^{4(m+1)}}\log\frac{2e}\varepsilon$ for all $N \ge 1$;
--   2. for every $\eta > 0$, $\mathbf P\big[\|A^N\| \ge \rho_m + \varepsilon\big] \ge \frac{1-\eta}{N^m}$ for all sufficiently large $N$.
--
--   Here $A^N$ is the random $2d$-regular adjacency matrix restricted to $\{1_N\}^\perp$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 10, Theorem 3.6 (the staircase theorem)

import Mathlib
import Definitions.Def_StrongConv

open Filter

namespace StrongConv

theorem prob_norm_adjPerp_ge_rhoStair (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ,
      (∀ m : ℕ, mStar d ≤ m → m ≤ d - 1 → ∀ ε : ℝ, 0 < ε →
        ε < rhoStair d (m + 1) - rhoStair d m → ∀ N : ℕ, 1 ≤ N →
        uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => rhoStair d m + ε ≤ ‖adjPerp σ‖) ≤
          C / ((N : ℝ) ^ m * ε ^ (4 * (m + 1))) * Real.log (2 * Real.exp 1 / ε)) ∧
      (∀ m : ℕ, mStar d ≤ m → m ≤ d - 1 → ∀ ε : ℝ, 0 < ε →
        ε < rhoStair d (m + 1) - rhoStair d m → ∀ η : ℝ, 0 < η →
        ∀ᶠ N : ℕ in atTop, (1 - η) / (N : ℝ) ^ m ≤
          uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => rhoStair d m + ε ≤ ‖adjPerp σ‖)) := by
  sorry

end StrongConv
