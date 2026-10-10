-- Prove2me | Theorems.Thm_ThomsonN7_Glue_capSpec_sound
-- name    : ThomsonN7.Glue.capSpec_sound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T01:45:50.139995+00:00
-- url     : https://prove2.me/theorems/0fa5c904-df66-46f9-808d-3c739f4872d7
-- title:
--   Thomson $N=7$: a cap specification implies the theorem on the cap
-- statement:
--   Let $a_0\in\mathbb R$ and suppose the *cap specification* at $a_0$ holds (reals $e,\delta,\tau$ with $\tau\le\tfrac1{165000}$, $E(P)\le e+\delta$, class minorants $H_A,H_B,H_C\le\varphi$ whose typed pair sum is at least $e$ on minimal-pair configurations with $\langle y_0,y_1\rangle\le a_0$, and whose slack $\varphi-H$ being at most $\delta$ forces the inner product within $\tau$ of $-1$, $0$, or one of $c_1=\cos\tfrac{2\pi}5$, $c_2=\cos\tfrac{4\pi}5$ respectively).
--
--   Then for every configuration $y$ of seven distinct unit vectors in $\mathbb R^3$ in which the pair $(0,1)$ realises the smallest inner product and $\langle y_0,y_1\rangle\le a_0$:
--
--   1. $$E(P)\ \le\ E(y);$$
--   2. if $E(y)=E(P)$, then $y_i=g(P_{\sigma(i)})$ for some linear isometry $g$ of $\mathbb R^3$ and some permutation $\sigma$ of $\{0,\dots,6\}$.
--
--   Here $P$ is the pentagonal bipyramid with the pentagon at indices $0,\dots,4$ and the poles at $5,6$, and $E(y)=\sum_{i<j}\|y_i-y_j\|^{-1}$.
--
--   This is the analytic half of the cap cell: it turns the near-sharp certificate into the sharp bound via tube rigidity of the bipyramid and its exact second-order local minimality.
--
--   **Formalization Note** `Glue.CapSpec`, `Glue.Concl`, `SphereConfig` and `pentBipyramid` come from the platform definition `ThomsonN7_core`, taken verbatim from the source.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package, https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §7.2 (steps 1–5); Lean `ThomsonN7.Glue.capSpec_sound`, https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L12729

import Definitions.Def_ThomsonN7_core

namespace ThomsonN7

theorem Glue.capSpec_sound {a0 : ℝ} (h : Glue.CapSpec a0) :
    ∀ y ∈ SphereConfig 7, inner ℝ (y 0) (y 1) ≤ a0 →
      (∀ i j, i ≠ j → inner ℝ (y 0) (y 1) ≤ inner ℝ (y i) (y j)) → Glue.Concl y := by sorry

end ThomsonN7
