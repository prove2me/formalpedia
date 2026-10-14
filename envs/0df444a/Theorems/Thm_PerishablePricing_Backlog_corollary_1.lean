-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_corollary_1
-- name    : PerishablePricing.Backlog.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:27:30.282232+00:00
-- url     : https://prove2.me/theorems/8eadc1e8-dee6-4c87-8da7-13b19e152ce4
-- title:
--   Corollary 1, p. 292 — monotone sensitivity of the order quantity and the demand level
-- statement:
--   In the backlogging model with the standing assumptions of §3 and §4, write the state also as $x = (x_1, \dots, x_{l-1})$ with $x_1 = s_1$ and $x_i = s_i - s_{i-1}$, so that raising $x_i$ by $\omega$ raises $s_j$ by $\omega$ for every $j \ge i$. Let $\hat x_{lt}(x) = s_{lt}(s) - s_{l-1}$ be the optimal order quantity and $\hat d_t(x) = d_t(s)$ the optimal demand level, where $(s_{lt}(s), d_t(s))$ is the largest optimal decision pair. For every period $t$ and $\omega \ge 0$,
--
--   $$-\omega \le \hat x_{lt}(x + \omega e_{l-1}) - \hat x_{lt}(x) \le \dots \le \hat x_{lt}(x + \omega e_1) - \hat x_{lt}(x) \le 0, \tag{10}$$
--
--   $$0 \le \hat d_t(x + \omega e_{l-1}) - \hat d_t(x) \le \dots \le \hat d_t(x + \omega e_1) - \hat d_t(x) \le \omega. \tag{11}$$
--
--   The optimal order quantity decreases in the inventory of each age, more slowly than one for one and more strongly for younger inventory; the optimal demand level (and so the discount offered) increases in the inventory of each age, most strongly for inventory close to expiry.
--
--   **Formalization Note** The chains are stated pairwise: for 0-based indices $i \le j$ and largest optimal pairs at $s$, at $s + \omega 1_{\ge i}$ and at $s + \omega 1_{\ge j}$ (the $s$-coordinates of $x + \omega e_i$ and $x + \omega e_j$), $-\omega \le \Delta_j \hat x \le \Delta_i \hat x \le 0$ and $0 \le \Delta_j \hat d \le \Delta_i \hat d \le \omega$, which is (10)–(11). The largest optimal pairs are hypotheses at the three points compared. The page's "for $t = 1, \dots, T+1$" covers only the decision periods $t \le T$ here, since there is no decision at $T + 1$; (11) prints $\hat d_{lt}$ for $\hat d_t$. The §4 assumption is the hypothesis $(1 - \gamma)c \le h^-$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Corollary 1, eqs. (10)–(11), p. 292 (PDF p. 10); x-coordinates, p. 289

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Model

namespace PerishablePricing.Backlog

/-- Corollary 1 (Monotone Sensitivity), p. 292, in the `s`-coordinates. Raising `x_i` by `ω`
(`x_1 = s_1`, `x_i = s_i − s_{i−1}`) raises `s_j` by `ω` for every `j ≥ i`; in 0-based indices this
is `s + ω·1_{≥ i}`. The optimal order quantity is `x̂ = s_{lt} − s_{l−1}` and the demand level is
`d̂ = d_t`. For `i ≤ j` (so `x + ωe_j` lies on the left of `x + ωe_i` in (10)–(11)) and `ω ≥ 0`,
with largest optimal decisions `(S, D)` at `s`, `(S_i, D_i)` at `s + ω·1_{≥ i}` and `(S_j, D_j)` at
`s + ω·1_{≥ j}`:
`−ω ≤ Δ_j x̂ ≤ Δ_i x̂ ≤ 0` and `0 ≤ Δ_j d̂ ≤ Δ_i d̂ ≤ ω`. -/
theorem corollary_1 {L k : ℕ} (M : Model L k) (hc : (1 - M.γ) * M.c ≤ M.hm) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ Model.StateSpace L) (ω : ℝ) (hω : 0 ≤ ω) (i j : Fin L)
    (hij : i ≤ j) (S D Si Di Sj Dj : ℝ)
    (hopt : M.IsLargestOptOrder n s S D)
    (hopt_i : M.IsLargestOptOrder n (s + fun m => if i ≤ m then ω else 0) Si Di)
    (hopt_j : M.IsLargestOptOrder n (s + fun m => if j ≤ m then ω else 0) Sj Dj) :
    let xhat : (Fin L → ℝ) → ℝ → ℝ := fun s' S' => S' - M.sLast s'
    let si : Fin L → ℝ := s + fun m => if i ≤ m then ω else 0
    let sj : Fin L → ℝ := s + fun m => if j ≤ m then ω else 0
    (-ω ≤ xhat sj Sj - xhat s S ∧ xhat sj Sj - xhat s S ≤ xhat si Si - xhat s S ∧
      xhat si Si - xhat s S ≤ 0 ∧
      0 ≤ Dj - D ∧ Dj - D ≤ Di - D ∧ Di - D ≤ ω) := by sorry

end PerishablePricing.Backlog
