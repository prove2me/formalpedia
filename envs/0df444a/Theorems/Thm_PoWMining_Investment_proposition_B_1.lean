-- Prove2me | Theorems.Thm_PoWMining_Investment_proposition_B_1
-- name    : PoWMining.Investment.proposition_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:39.904736+00:00
-- url     : https://prove2.me/theorems/4cd17b3f-621c-49eb-8ec4-70bc4c2f52dc
-- title:
--   Proposition B.1, p. 43 — at a fixed active set, ∂π*_i/∂c_i < 0 and ∂π*_i/∂c_j > 0
-- statement:
--   Let $n\ge2$ miners be active with costs $c_1,\dots,c_n>0$, reward $R>0$ and capacity parameter $\gamma\ge0$, and let $g$, $f_i$ and $\pi^*_i=\frac{R}{g}f_i-c_if_i-\frac{\gamma}{2}f_i^2$ be the closed forms of (B.3). Assume all $n$ miners are active, i.e. $R-c_kg>0$ for every $k$. Then, for every miner $i$ and every other miner $j\ne i$, the profit $\pi^*_i$ is differentiable in $c_i$ and in $c_j$ (the other costs held fixed), and
--
--   $$
--   \frac{\partial\pi^*_i}{\partial c_i}<0,\qquad \frac{\partial\pi^*_i}{\partial c_j}>0 .
--   $$
--
--   So, as long as the set of active miners does not change, a miner's equilibrium profit falls when its own cost rises and rises when a rival's cost rises. The proof of Proposition 5.1 uses this to argue that an active miner invests to minimize its own cost.
--
--   **Formalization Note** Each partial derivative is the derivative of $t\mapsto\pi^*_i(c_1,\dots,t,\dots,c_n)$ at $t=c_i$ (resp. $c_j$), stated as `HasDerivAt` with an existentially quantified value of the stated sign, so a non-differentiable point cannot make the claim hold by Lean's junk value of `deriv`. The derivative is local, at a fixed active set, as printed. Lean indices are 0-based.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 43, Proposition B.1

import Mathlib
import Definitions.Def_PoWMining_Investment_ClosedForm

namespace PoWMining.Investment

/-- Proposition B.1 (p. 43): for `n ≥ 2` active miners with costs `c : Fin n → ℝ`, all active
(`R - c_k g > 0` for every `k`), the equilibrium profit `π*_i` of (B.3) strictly decreases in
the own cost `c_i` and strictly increases in every rival cost `c_j`, `j ≠ i` (derivatives at a
fixed active set). -/
theorem proposition_B_1 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hn : 2 ≤ n) (hR : 0 < R)
    (hγ : 0 ≤ γ) (hc : ∀ k, 0 < c k) (hact : ∀ k, 0 < R - c k * PoWMining.CostStatics.gH c γ R) (i : Fin n) :
    (∃ d : ℝ, HasDerivAt (fun t => profitH (Function.update c i t) γ R i) d (c i) ∧ d < 0) ∧
    (∀ j : Fin n, j ≠ i →
      ∃ d : ℝ, HasDerivAt (fun t => profitH (Function.update c j t) γ R i) d (c j) ∧ 0 < d) := by sorry

end PoWMining.Investment
