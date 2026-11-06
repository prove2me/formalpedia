-- Prove2me | Theorems.Thm_QGChasing_lemma_3_1
-- name    : QGChasing.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:31.441237+00:00
-- url     : https://prove2.me/theorems/b63829f0-4815-4cac-82c6-afa4d5d4f519
-- title:
--   Lemma 3.1 — $\|\nabla f(x)\|^2\le 2L(f(x)-f^\star)$ for $L$-smooth $f$
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be $L$-smooth for some $L>0$ (differentiable with $L$-Lipschitz gradient), and suppose $f$ attains its global minimum value $f^\star=f(x^\star)$. Then for every $x\in\mathbb R^d$,
--   $$
--   \|\nabla f(x)\|^2\le 2L\big(f(x)-f^\star\big).
--   $$
--   Convexity is not assumed. The lemma converts the suboptimality of a smooth cost into a bound on its gradient; the proof of Lemma 4.2 uses it to bound $\|\nabla g_t(y_t)\|$.
--
--   Differences from the source:
--   - encoding: f attains its global minimum value f⋆ → a point xs with f xs ≤ f z for all z, and f⋆ = f xs; reason: a value is attained exactly when it is f at some minimizer
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Lemma 3.1, p.4

import Mathlib
import Definitions.Def_HomotopyProxVM_IsSmoothParam

namespace QGChasing

/-- **Lemma 3.1** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.4). Let `f : ℝᵈ → ℝ` be `L`-smooth for some `L > 0` and attain its
global minimum value `f⋆` (at `xs`). Then `‖∇f(x)‖² ≤ 2L(f(x) − f⋆)` for every `x ∈ ℝᵈ`.

**Formalization Note** `L`-smoothness is the published `HomotopyProxVM.IsSmoothParam` (Assumption
5's condition). Convexity is not assumed, as on the page. -/
theorem lemma_3_1 {d : ℕ} (L : ℝ) (hL : 0 < L) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : HomotopyProxVM.IsSmoothParam f L) (xs : EuclideanSpace ℝ (Fin d)) (hxs : ∀ z, f xs ≤ f z) (x : EuclideanSpace ℝ (Fin d)) :
    ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - f xs) := by sorry

end QGChasing
