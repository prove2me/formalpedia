-- Prove2me | Theorems.Thm_SilverRateLB_eq_14_cost_bound
-- name    : SilverRateLB.eq_14_cost_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:06.826277+00:00
-- url     : https://prove2.me/theorems/5c4398b1-7d5a-4cf9-95d1-621b66f335a1
-- title:
--   (14) — $\mathscr R_n(H)\ge c^2(\Lambda-1)/Q_\Lambda(T;H)^2$
-- statement:
--   Let $\varepsilon,\gamma>0$ with constants $a,c$ of Lemma 2.4 and let $\Lambda\ge a$. For every nonnegative schedule $H$ and admissible checkpoint set $T$,
--   $$\mathscr R_n(H)\ \ge\ \frac{c^2(\Lambda-1)}{Q_\Lambda(T;H)^2},\tag{14}$$
--   where $Q_\Lambda(T;H)$ is the checkpoint cost (13).
--
--   Maximizing the right-hand side over $T$ is minimizing the cost, so $\mathscr R_n(H)\ge c^2(\Lambda-1)/V_\Lambda(H)^2$.
--
--   Differences from the source:
--   - encoding: ℛ_n with the paper's convention L = 1 (footnote 6, p. 6) → worstCaseRate 1; reason: the paper works with L = 1 in Sections 2–3 and the proofs; footnote 6 reduces every L to it
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n → H : List ℝ with nonnegative entries, n = H.length; reason: same schedules
--   - generalization: 0 < ε < 1/2, γ > 0 (fixed in §3.2) → ε > 0, γ > 0; reason: (14) follows from Lemma 2.4, which holds for all ε, γ > 0; the paper's range is a special case
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §3.2, (14), p. 13; proof §B.1, p. 26

import Mathlib
import Definitions.Def_SilverRateLB_aOf
import Definitions.Def_SilverRateLB_V
import Definitions.Def_SilverRateLB_worstCaseRate

namespace SilverRateLB

/-- **(14): the bound in terms of the checkpoint cost.** With `a`, `c` as in Lemma 2.4, every
nonnegative schedule `H`, admissible checkpoint set `T` and `Λ ≥ a` satisfy
`ℛ_n(H) ≥ c²(Λ − 1)/Q_Λ(T; H)²`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §3.2, (14), p. 13 (proof §B.1, p. 26).

**Formalization Note** `ℛ_n` is `worstCaseRate 1` (footnote 6). The paper fixes `0 < ε < 1/2` in
§3.2; the statement is for every `ε, γ > 0`, the range of Lemma 2.4 from which it follows. -/
theorem eq_14_cost_bound (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (H : List ℝ)
    (hH : ∀ h ∈ H, 0 ≤ h) (T : Finset ℕ) (hT : IsAdmissible H T) (Λ : ℝ) (hΛ : aOf ε γ ≤ Λ) :
    ENNReal.ofReal (cOf ε γ ^ 2 * (Λ - 1) / ckptCost (aOf ε γ) (cOf ε γ) Λ H T ^ 2)
      ≤ worstCaseRate 1 H := by sorry

end SilverRateLB
