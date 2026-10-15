-- Prove2me | Theorems.Thm_Plasticity_Ext_KMRate
-- name    : Plasticity.Ext.KMRate
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T17:55:19.88537+00:00
-- url     : https://prove2.me/theorems/504d10a2-9490-4064-aeb7-8e1f23056e47
-- title:
--   Rate of asymptotic regularity for the Krasnoselskii–Mann iteration with constant step (Baillon–Bruck)
-- statement:
--   Let $C$ be a convex subset of a real normed space with $\|x-y\|\le D$ for all $x,y\in C$, let $K\colon C\to C$ be nonexpansive, let $0<\alpha<1$, and let $P=(1-\alpha)I+\alpha K$. Then for every $x\in C$ and every $n\ge1$,
--   $$\bigl\|P^n(x)-K(P^n(x))\bigr\|\le\frac{D}{\sqrt{\pi\,n\,\alpha(1-\alpha)}}.$$
--   The iterates $x_n=P^n(x)$ are the Krasnoselskii–Mann iterates $x_{k}=(1-\alpha)x_{k-1}+\alpha Kx_{k-1}$ with constant step $\alpha$, so this is the bound $\|x_n-Kx_n\|\le\operatorname{diam}(C)/\sqrt{\pi\sum_{i=1}^n\alpha_i(1-\alpha_i)}$ for $\alpha_i\equiv\alpha$. The space need not be complete, and $K$ need not have a fixed point.
-- source:
--   J.-B. Baillon and R. E. Bruck, The rate of asymptotic regularity is O(1/√n), in: Theory and Applications of Nonlinear Operators of Accretive and Monotone Type, Lecture Notes in Pure and Applied Mathematics 178, Dekker, New York (1996), pp. 51–81 (constant step); R. Cominetti, J. A. Soto and J. Vaisman, On the rate of convergence of Krasnosel'skii–Mann iterations and their connection with sums of Bernoullis, Israel J. Math. 199 (2014), 757–772, Theorem 1 with α_i ≡ α (arXiv:1206.4195)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Ext
theorem KMRate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (D : ℝ) (hD : ∀ x ∈ C, ∀ y ∈ C, ‖x - y‖ ≤ D)
    (K : E → E) (hmaps : Set.MapsTo K C C) (hlip : LipschitzOnWith 1 K C)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (hn : 1 ≤ n) (x : E) (hx : x ∈ C) :
    ‖(fun z => (1 - α) • z + α • K z)^[n] x - K ((fun z => (1 - α) • z + α • K z)^[n] x)‖
      ≤ D / Real.sqrt (Real.pi * n * α * (1 - α)) := by sorry
end Plasticity.Ext
