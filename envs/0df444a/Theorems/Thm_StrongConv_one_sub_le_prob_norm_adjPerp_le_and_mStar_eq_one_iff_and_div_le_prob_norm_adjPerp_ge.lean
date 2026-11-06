-- Prove2me | Theorems.Thm_StrongConv_one_sub_le_prob_norm_adjPerp_le_and_mStar_eq_one_iff_and_div_le_prob_norm_adjPerp_ge
-- name    : StrongConv.one_sub_le_prob_norm_adjPerp_le_and_mStar_eq_one_iff_and_div_le_prob_norm_adjPerp_ge
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:49.907572+00:00
-- url     : https://prove2.me/theorems/2f6c48a8-871c-4811-896d-a16f94a3882b
-- title:
--   Remark 3.7 — ‖A^N‖ ≤ 2√(2d−1) + ε with probability 1 − c/N^{m*}, and the 1/N rate of Theorem 3.4 is sharp for 2 ≤ d ≤ 4
-- statement:
--   Let $d \ge 2$, let $A^N = S_1^N + S_1^{N*} + \cdots + S_d^N + S_d^{N*}$ be the adjacency matrix of the random $2d$-regular graph on $N$ vertices (permutation model) restricted to $\{1_N\}^\perp$, and let $\rho_m$ and $m_* = \lfloor\frac12(\sqrt{2d-1}+1)\rfloor$ be as in Theorem 3.6 (`rhoStair d m`, `mStar d`). Then:
--   1. for every $\varepsilon > 0$ there is a constant $c$ such that $\mathbf P\big[\|A^N\| \le 2\sqrt{2d-1} + \varepsilon\big] \ge 1 - \frac{c}{N^{m_*}}$ for all $N \ge 1$;
--   2. $m_* = 1$ if and only if $d \le 4$;
--   3. if $m_* = 1$, then for every $0 < \varepsilon < \rho_2 - \rho_1$ there is a constant $c > 0$ such that $\mathbf P\big[\|A^N\| \ge 2\sqrt{2d-1} + \varepsilon\big] \ge \frac cN$ for all sufficiently large $N$.
--
--   The constants $c$ may depend on $d$ and $\varepsilon$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 11, Remark 3.7

import Mathlib
import Definitions.Def_StrongConv

open Filter

namespace StrongConv

theorem one_sub_le_prob_norm_adjPerp_le_and_mStar_eq_one_iff_and_div_le_prob_norm_adjPerp_ge
    (d : ℕ) (hd : 2 ≤ d) :
    (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ N : ℕ, 1 ≤ N →
      1 - c / (N : ℝ) ^ mStar d ≤
        uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖adjPerp σ‖ ≤ 2 * Real.sqrt (2 * d - 1) + ε)) ∧
    (mStar d = 1 ↔ d ≤ 4) ∧
    (mStar d = 1 → ∀ ε : ℝ, 0 < ε → ε < rhoStair d 2 - rhoStair d 1 →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
        c / (N : ℝ) ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖)) := by
  sorry

end StrongConv
