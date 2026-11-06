-- Prove2me | Theorems.Thm_PrefixVR_eq_42
-- name    : PrefixVR.eq_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:00.350337+00:00
-- url     : https://prove2.me/theorems/0c298909-ba5c-4877-b08b-f42985926cb5
-- title:
--   Eq. (42) — the pathwise descent inequality
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be $L_f$-smooth: differentiable, with $\|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|$ for all $x,y$. For every $x,v\in\mathbb R^d$ and every $\eta$, with $x^+=x-\eta v$ and $e=v-\nabla f(x)$,
--   $$
--   f(x^+)\le f(x)-\frac\eta2\|\nabla f(x)\|^2-\frac\eta2(1-L_f\eta)\|v\|^2+\frac\eta2\|e\|^2 .\qquad(42)
--   $$
--   Applied to $x=x_t$, $v=v_t$ of Algorithm 1 ($x_{t+1}=x_t-\eta v_t$, $e_t=v_t-\nabla f(x_t)$), this is the per-step inequality behind Theorems 1 and 2.
--
--   **Formalization Note** $L_f$-smoothness is the published `IsBetaSmooth f G Lf` with gradient map $G=\nabla f$ (which includes $L_f\ge0$).
--
--   Differences from the source:
--   - generalization: x = x_t, v = v_t of a run of Algorithm 1, η > 0, L_f > 0 → every x, v ∈ ℝᵈ, every real η, every L_f ≥ 0; reason: the inequality is deterministic; the source's case is an instance
--   - encoding: f is L_f-smooth → IsBetaSmooth f G Lf; reason: published definition: gradient G everywhere, Lf-Lipschitz
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), App. C, Eq. (42), p.15 (PDF p.15)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs

namespace PrefixVR

/-- **The pathwise descent inequality (42).** Jiang, Wang, Yang, Li, Zhang (manuscript, sha256
ed33106a…), App. C, Eq. (42), p.15: by `L_f`-smoothness and `x_{t+1} − x_t = −ηv_t`, with
`e_t = v_t − ∇f(x_t)`,
`f(x_{t+1}) ≤ f(x_t) − (η/2)‖∇f(x_t)‖² − (η/2)(1 − L_f η)‖v_t‖² + (η/2)‖e_t‖²`.

Stated for every `L_f`-smooth `f` (gradient map `G`), every point `x`, every direction `v` and
every real `η`, with `x⁺ = x − ηv`.

**Formalization Note.** `L_f`-smoothness is the published `ConvexOptAlg.SmoothGD.IsBetaSmooth f G Lf`
(`f` has gradient `G x` at every `x`, `G` is `Lf`-Lipschitz, `Lf ≥ 0`). -/
theorem eq_42 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Lf : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f G Lf) (x v : EuclideanSpace ℝ (Fin d)) (η : ℝ) :
    f (x - η • v) ≤ f x - η / 2 * ‖G x‖ ^ 2 - η / 2 * (1 - Lf * η) * ‖v‖ ^ 2
      + η / 2 * ‖v - G x‖ ^ 2 := by sorry

end PrefixVR
