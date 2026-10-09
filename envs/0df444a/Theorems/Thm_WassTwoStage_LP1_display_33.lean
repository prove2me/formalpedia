-- Prove2me | Theorems.Thm_WassTwoStage_LP1_display_33
-- name    : WassTwoStage.LP1.display_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:57:48.97342+00:00
-- url     : https://prove2.me/theorems/affccf8f-6de1-4195-b280-1c1d4e02b176
-- title:
--   Display (33) — the worst-case expectation as a robust problem with the constraint $\|T(x)^\top p\|_* \le \lambda$
-- statement:
--   In the setting of Section 4 ($Q=0$, $\Xi=\mathbb R^K$, 1-Wasserstein ball with the gauge (31), $w_+,w_->0$, $I\ge 1$ samples, sufficiently expensive recourse), let $\epsilon>0$. Then for every $x\in\mathcal X$
--
--   $$\mathcal Z(x) = \inf\ \epsilon\lambda + \frac1I\sum_{i\in[I]}\ \sup_{\substack{p\ge 0\\ W^\top p = q}}\ h(x)^\top p + (T(x)^\top p)^\top\hat\xi_i \quad\text{s.t.}\quad \lambda\in\mathbb R_+,\ \ \|T(x)^\top p\|_*\le\lambda\ \ \forall p\in\mathbb R^M_+ : W^\top p = q, \qquad (33)$$
--
--   where $\|\cdot\|_*$ is the dual norm of (31). This is the intermediate formulation of the proof of Theorem 6: the inner suprema are the recourse values at the samples, and the semi-infinite constraint carries the whole effect of the ambiguity set.
--
--   **Formalization Note** The inner suprema and the infimum are extended reals; if no $\lambda$ satisfies the constraint the value is $+\infty$. The hypothesis $\epsilon>0$ is needed: Theorem 1's dual (6), from which (33) is derived, is stated only for $\epsilon>0$, and at $\epsilon=0$ the identity can fail (the right-hand side can be $+\infty$ while $\mathcal Z(x)$ is the finite sample average).
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, §4.1, proof of Theorem 6, display (33), p. 23

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge
import Definitions.Def_WassTwoStage_LP1_Setting
import Definitions.Def_WassTwoStage_LP1_Reformulations

open MeasureTheory Matrix

namespace WassTwoStage.LP1

/-- Display (33), proof of Theorem 6, Hanasusanto–Kuhn, arXiv:1609.07505v3, §4.1, p. 23: under
the standing assumptions of §4 (`Q = 0`, `Ξ = ℝ^K`, 1-Wasserstein ball with the gauge (31),
sufficiently expensive recourse) and `ε > 0`, the worst-case expectation equals
`inf {ελ + (1/I) Σ_i sup_{p ≥ 0, Wᵀp = q} h(x)ᵀp + (T(x)ᵀp)ᵀξ̂_i : λ ∈ ℝ_+,
‖T(x)ᵀp‖_* ≤ λ ∀ p ∈ ℝ^M_+ with Wᵀp = q}`. -/
theorem display_33 {K M N₁ N₂ I : ℕ} (d : Data K M N₁ N₂ I) (hI : 0 < I) (hε : 0 < d.ε)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse)
    (x : Fin N₁ → ℝ) (hx : x ∈ d.X) :
    d.worstCase x = d.value33 x := by sorry

end WassTwoStage.LP1
