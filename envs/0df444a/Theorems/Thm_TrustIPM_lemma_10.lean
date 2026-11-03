-- Prove2me | Theorems.Thm_TrustIPM_lemma_10
-- name    : TrustIPM.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:00.333193+00:00
-- url     : https://prove2.me/theorems/0759a37b-215e-4281-b2a8-6277ebc461a1
-- title:
--   Lemma 10 — one Take-step decreases $\psi_\mu$ by the predicted progress up to $\tfrac73\mu\eta^3$
-- statement:
--   Suppose Assumptions 1 and 3 hold. Let $x\in\mathcal X$, $\eta\in[0,1/5]$, and let $(x^+,y^+)$ be an output of Take-step$(f,a,\mu,x,\eta)$ with direction $d_x$. Then
--
--   1. $\mathrm{Convex}\{x,x^+\}\subseteq\mathcal X$, and
--   2. $$\psi_\mu(x^+)-\psi_\mu(x)\le\frac73\mu\eta^3+\max\Bigl\{\mathcal M^{\psi_\mu}_x(d_x),-\frac{\eta^2\mu}3\Bigr\} .\tag{22}$$
--
--   The iterates therefore stay strictly feasible, and an iteration with a large predicted decrease reduces the barrier.
--
--   Differences from the source:
--   - encoding: (x⁺, y⁺) ← Take-step(f, a, µ, x, η) → IsTakeStep for every argmin selection d_x, with α = 1 when S⁻¹d_s = 0; reason: Take-step chooses any element of the argmin; η/0 = +∞ on the page
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 10, p.15

import Mathlib
import Definitions.Def_TrustIPM_IsTakeStep

namespace TrustIPM

/-- **Lemma 10** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 10, p.15). Suppose Assumptions 1 and 3 hold. Let
`x ∈ X`, `η ∈ [0, 1/5]`, `(x⁺, y⁺) ← Take-step(f, a, µ, x, η)`. Then `Convex{x, x⁺} ⊆ X` and
`ψµ(x⁺) − ψµ(x) ≤ (7/3)µη³ + max{M^{ψµ}_x(d_x), −η²µ/3}` (22).

**Formalization Note** The statement covers every output of Take-step, i.e. every direction
`d_x ∈ argmin_{u ∈ B_r(0)} M^{ψµ}_x(u)` (`IsTakeStep`). `µ > 0` follows from Assumption 3
(`L₂²µ/L₁³ > 0`); `n, m` are positive integers (p.1). -/
theorem lemma_10 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (f : E n → ℝ) (a : Fin m → E n → ℝ)
    (L₁ L₂ μ τl η : ℝ) (x d xp : E n) (yp : Fin m → ℝ) (hA1 : Assumption1 f a L₁ L₂)
    (hA3 : Assumption3 L₁ L₂ μ τl) (hx : x ∈ feasibleSet a) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 5)
    (hstep : IsTakeStep f a μ L₁ η x d xp yp) :
    segment ℝ x xp ⊆ feasibleSet a ∧
      barrier f a μ xp - barrier f a μ x ≤
        7 / 3 * μ * η ^ 3 + max (model f a μ x d) (-(η ^ 2 * μ) / 3) := by sorry

end TrustIPM
