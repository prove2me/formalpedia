-- Prove2me | Theorems.Thm_RobustMNL_SizeCon_rectangular_unconstrained
-- name    : RobustMNL.SizeCon.rectangular_unconstrained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:17.554547+00:00
-- url     : https://prove2.me/theorems/05e5ebd5-8d52-4746-ae22-71ef531e8d1c
-- title:
--   Example 3.4, p. 8 — for V = ∏[l_i, u_i], Z*(V) = max_{S⊆A} f(S, (u₀, l₁, …, lₙ))
-- statement:
--   Let $\mathcal V=\prod_{i=0}^n [l_i,u_i]\subseteq\mathbb R^{n+1}_{++}$ be a rectangular uncertainty set ($0<l_0\le u_0$, $0<l_i\le u_i$) and $r_1,\dots,r_n$ real revenues. Then the optimal value of the (unconstrained) robust assortment problem equals the optimal revenue under the known parameter vector $h=(u_0,l_1,\dots,l_n)$:
--
--   $$
--   Z^*(\mathcal V)=\max_{S\subseteq\mathcal A}\ \min_{v\in\mathcal V} f(S,v)=\max_{S\subseteq\mathcal A} f\big(S,(u_0,l_1,l_2,\dots,l_n)\big).
--   $$
--
--   In words, the adversary facing a box picks the largest no-purchase weight and the smallest product weights, and the robust problem is an ordinary MNL assortment problem with these weights. It is the special case $K\ge n$ of Theorem 3.8, which the paper establishes independently in Example 3.4.
--
--   **Formalization Note** The paper states the chain $Z^*(\mathcal V)=\max_S f(S,h)=f(S^*_h,h)$; the last expression is $\max_S f(S,h)$ by the definition of $S^*_h$ as an optimal assortment under $h$, so the Lean statement keeps the first equality, the mathematical content. The minimum is a real infimum over the box; $l_0\le u_0$ and $l\le u$ say the intervals are nonempty. Revenues are arbitrary reals. Products are 0-indexed (`Fin n`).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Example 3.4, p. 8, displayed claim

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_RobustMNL_SizeCon_Model

namespace RobustMNL.SizeCon

/-- Example 3.4, p. 8: over the rectangular set `∏_{i=0}^n [l_i, u_i] ⊆ ℝⁿ⁺¹₊₊`,
`Z*(V) = max_{S ⊆ 𝒜} min_{v ∈ V} f(S, v) = max_{S ⊆ 𝒜} f(S, (u₀, l₁, …, lₙ))`. -/
theorem rectangular_unconstrained {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hlu₀ : l₀ ≤ u₀) (hl : ∀ i, 0 < l i) (hlu : l ≤ u) (r : Fin n → ℝ) :
    RobustMNL.Static.Zstar (box l₀ u₀ l u) r =
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
        (fun S => RobustMNL.Static.rev r S (u₀, l)) := by sorry

end RobustMNL.SizeCon
