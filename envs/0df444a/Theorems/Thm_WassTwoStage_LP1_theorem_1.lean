-- Prove2me | Theorems.Thm_WassTwoStage_LP1_theorem_1
-- name    : WassTwoStage.LP1.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:57:18.57698+00:00
-- url     : https://prove2.me/theorems/8ae97f04-3eba-4456-bbcf-360a97dbba8d
-- title:
--   Theorem 1 (§4 instance) — worst-case expectation = moment problem (5) = dual (6) for the gauge-cost 1-Wasserstein ball
-- statement:
--   Consider the two-stage distributionally robust linear program of Section 4: the uncertainty affects only the recourse constraints ($Q=0$), the support is $\Xi=\mathbb R^K$, and the ambiguity set is the 1-Wasserstein ball of radius $\epsilon\ge 0$ around the empirical distribution $\hat{\mathbb P}_I$ of $I\ge 1$ samples, with reference distance $d(\xi,\xi') = \|\xi-\xi'\|$ for the gauge (31), $w_+,w_->0$. Assume sufficiently expensive recourse ($\exists p\ge 0$ with $W^\top p = q$). Then for every $x\in\mathcal X$ the worst-case expectation coincides with the optimal value of the generalized moment problem
--
--   $$\mathcal Z(x) = \sup\ \frac1I\sum_{i\in[I]}\int Z(x,\xi)\,\mathbb P_i(d\xi)\quad\text{s.t.}\quad \mathbb P_i\in\mathcal M^1(\mathbb R^K)\ \forall i,\ \ \frac1I\sum_{i\in[I]}\int\|\xi-\hat\xi_i\|\,\mathbb P_i(d\xi)\le\epsilon, \qquad (5)$$
--
--   and, if $\epsilon>0$, with the optimal value of the dual robust optimization problem
--
--   $$\mathcal Z(x) = \inf_{\lambda\in\mathbb R_+}\ \epsilon\lambda + \frac1I\sum_{i\in[I]}\sup_{\xi\in\mathbb R^K}\big[Z(x,\xi) - \lambda\|\xi-\hat\xi_i\|\big]. \qquad (6)$$
--
--   This is the instance ($r=1$, gauge cost, $\Xi=\mathbb R^K$) of Theorem 1 that the proof of Theorem 6 starts from.
--
--   **Formalization Note** Definition 3 and Theorem 1 of the paper speak of a metric $d$; for $w_+\ne w_-$ the cost (31) is not symmetric, and this statement is the application the paper makes in the proof of Theorem 6 ("Theorem 1 thus implies"). Duality of this form holds for any nonnegative lower semicontinuous cost vanishing on the diagonal. All values are extended reals; the recourse value may be $+\infty$ at some $\xi$, in which case both sides are $+\infty$ when $\epsilon>0$.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 7, Theorem 1 (proof p. 38), applied on p. 23 in the setting of §4 (p. 22)

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge
import Definitions.Def_WassTwoStage_LP1_Setting
import Definitions.Def_WassTwoStage_LP1_Reformulations

open MeasureTheory Matrix

namespace WassTwoStage.LP1

/-- Theorem 1, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 7 (proof p. 38), in the instance of §4
(p. 22): `Q = 0`, `Ξ = ℝ^K`, the 1-Wasserstein ball (`r = 1`) with reference cost
`d(ξ, ξ') = ‖ξ − ξ'‖` for the gauge (31), and sufficiently expensive recourse. The worst-case
expectation `𝒵(x)` equals the value of the moment problem (5), and for `ε > 0` it equals the value
of the dual problem (6). -/
theorem theorem_1 {K M N₁ N₂ I : ℕ} (d : Data K M N₁ N₂ I) (hI : 0 < I) (hε : 0 ≤ d.ε)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse)
    (x : Fin N₁ → ℝ) (hx : x ∈ d.X) :
    d.worstCase x = d.momentValue x ∧ (0 < d.ε → d.worstCase x = d.dualValue6 x) := by sorry

end WassTwoStage.LP1
