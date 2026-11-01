-- Prove2me | Theorems.Thm_TimeVaryingGames_bregman_lower_bound
-- name    : TimeVaryingGames.bregman_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:26.384605+00:00
-- url     : https://prove2.me/theorems/26496888-2080-46f0-8b39-135bc4086d13
-- title:
--   Footnote 4, p.10: $D(p,x)\ge(K/2)\|x-p\|^2$, so $D(p,x_t)\to0$ forces $x_t\to p$
-- statement:
--   Let $h$ be a distance-generating function with modulus $K$ on a compact convex set $\mathcal C$, with Bregman divergence $D$, and let $p\in\mathcal C$. Then:
--
--   1. $D(p,x)\ge\frac K2\|x-p\|^2$ for every $x$ in the prox-domain $\mathcal C_h$;
--   2. every sequence $x_t\in\mathcal C_h$ with $D(p,x_t)\to0$ converges to $p$.
--
--   Together with the reciprocity condition (RC), this shows that $x_t\to p$ if and only if $D(p,x_t)\to0$, which is how convergence of the energy is turned into convergence of the iterates.
--
--   Differences from the source:
--   - encoding: h : X → ℝ ∪ {∞} with dom h = C; ∂h(x) tested against all x′ ∈ X → h : E → ℝ with only its values on C used; the subgradient inequality tested for x′ ∈ C; reason: h = +∞ off C, so the inequality is automatic off C: the same subdifferential and prox-domain
--   - encoding: there exists a continuous selection ∇h of ∂h on dom ∂h → the selection is a parameter gradh with ContinuousOn and gradh x ∈ ∂h(x) on the prox-domain; reason: D and P are defined through the selection, so it must be fixed data
--   - encoding: K-strongly convex with modulus K (divided by in (A.5b), (40)) → 0 < Kc is part of IsDGF; reason: a strong-convexity modulus is positive; the paper divides by it
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, footnote 4, p.10

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

open Filter Topology

namespace TimeVaryingGames

/-- **The Bregman divergence dominates the squared distance** (footnote 4).
arXiv:1809.03066v3, footnote 4, p.10: "Indeed, D(p, x_t) = h(p) − h(x_t) − ⟨∇h(x_t), p − x_t⟩
≥ (K/2)‖x_t − p‖², so x_t → p whenever D(p, x_t) → 0."

For a DGF `h` on the compact convex `C` with modulus `K` and a point `p ∈ C`:
1. `D(p, x) ≥ (K/2)‖x − p‖²` for every `x` in the prox-domain;
2. every sequence `x_t` in the prox-domain with `D(p, x_t) → 0` converges to `p`. -/
theorem bregman_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} {Kc : ℝ} {h : E → ℝ} {gradh : E → E →L[ℝ] ℝ}
    (hdgf : IsDGF C Kc h gradh) {p : E} (hp : p ∈ C) :
    (∀ x ∈ proxDomain C h, Kc / 2 * ‖x - p‖ ^ 2 ≤ bregman h gradh p x) ∧
      ∀ xt : ℕ → E, (∀ t, xt t ∈ proxDomain C h) →
        Tendsto (fun t => bregman h gradh p (xt t)) atTop (𝓝 0) → Tendsto xt atTop (𝓝 p) := by sorry

end TimeVaryingGames
