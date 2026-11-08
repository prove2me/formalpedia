-- Prove2me | Theorems.Thm_QGChasing_normalization
-- name    : QGChasing.normalization
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:25:51.254097+00:00
-- url     : https://prove2.me/theorems/3da5cfe8-a4a2-4a68-9a40-262766d42663
-- title:
--   Proof of Theorem 1.1 — normalization: a $C$-competitive bound for $g_t=f_t-f_t(v_t)$ gives one for $f_t$
-- statement:
--   Let $C\ge1$, let $f_1,f_2,\dots$ be nonnegative functions on $\mathbb R^d$, let $v_1,v_2,\dots$ be points, and write $g_t=f_t-f_t(v_t)$. If decision sequences $x$ and $u$ satisfy, for a horizon $T$,
--   $$
--   \sum_{t=1}^T\big(g_t(x_t)+\|x_t-x_{t-1}\|\big)\le C\sum_{t=1}^T\big(g_t(u_t)+\|u_t-u_{t-1}\|\big),
--   $$
--   then
--   $$
--   \sum_{t=1}^T\big(f_t(x_t)+\|x_t-x_{t-1}\|\big)\le C\sum_{t=1}^T\big(f_t(u_t)+\|u_t-u_{t-1}\|\big).
--   $$
--   This is the first step of the proof of Theorem 1.1: it reduces the competitive analysis to the shifted costs $g_t$, which vanish at the minimizers.
--
--   Differences from the source:
--   - generalization: v_t the global minimizer of f_t ∈ F_κ; x the algorithm's decisions; u a feasible comparator with u_0 = x_0 → any points v_t, any nonnegative f_t (t ≥ 1), any sequences x and u; reason: the step uses only C ≥ 1 and f_t(v_t) ≥ 0; the page's setting is an instance
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), proof of Theorem 1.1, normalization, pp.6–7

import Mathlib
import Definitions.Def_QGChasing_chasingCost

namespace QGChasing

/-- **Proof of Theorem 1.1, normalization** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), pp.6–7). If an online algorithm's decisions
`x` satisfy the `C`-competitive bound for the shifted costs `g_t = f_t − f_t(v_t)` against a
comparator `u`,
`∑_{t=1}^T (g_t(x_t) + ‖x_t − x_{t−1}‖) ≤ C ∑_{t=1}^T (g_t(u_t) + ‖u_t − u_{t−1}‖)`,
and `C ≥ 1` and every `f_t` is nonnegative, then the same bound holds for the original costs `f_t`.

**Formalization Note** The points `v_t` are arbitrary and the comparator is unrestricted: the step
uses only `C ≥ 1` and `f_t(v_t) ≥ 0`. -/
theorem normalization {d : ℕ} (C : ℝ) (hC : 1 ≤ C) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ∀ t, 1 ≤ t → ∀ z, 0 ≤ f t z) (v x u : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ)
    (h : ∑ t ∈ Finset.range T,
          ((f (t + 1) (x (t + 1)) - f (t + 1) (v (t + 1))) + ‖x (t + 1) - x t‖) ≤
        C * ∑ t ∈ Finset.range T,
          ((f (t + 1) (u (t + 1)) - f (t + 1) (v (t + 1))) + ‖u (t + 1) - u t‖)) :
    chasingCost f x T ≤ C * chasingCost f u T := by sorry

end QGChasing
