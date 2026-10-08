-- Prove2me | Theorems.Thm_RobustMNL_SizeCon_rectangular_reduction
-- name    : RobustMNL.SizeCon.rectangular_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:16.849975+00:00
-- url     : https://prove2.me/theorems/47efde76-a3d7-466a-a8bc-3c150fd998d9
-- title:
--   Proof of Theorem 3.8, p. 12 — for a box, max_{|S|≤K} min_v (1/v₀) Σ v_i (r_i − λ) = max_{|S|≤K} (1/u₀) Σ l_i (r_i − λ)
-- statement:
--   Let $\mathcal V=\prod_{i=0}^n [l_i,u_i]\subseteq\mathbb R^{n+1}_{++}$ be a rectangular uncertainty set: $0<l_0\le u_0$ and $0<l_i\le u_i$ for every product $i$, the no-purchase weight $v_0$ ranges over $[l_0,u_0]$ and the weight $v_i$ of product $i$ over $[l_i,u_i]$. Let $r_1,\dots,r_n$ be real revenues and $K\in\mathbb N$. Then for every real $\lambda$,
--
--   $$
--   \max_{S:\ |S|\le K}\ \min_{v\in\mathcal V}\ \frac{1}{v_0}\sum_{i\in S} v_i\,(r_i-\lambda)
--   \;=\;\max_{S:\ |S|\le K}\ \frac{1}{u_0}\sum_{i\in S} l_i\,(r_i-\lambda).
--   $$
--
--   The right-hand side is the same parametric quantity evaluated at the single parameter vector $(u_0,l_1,\dots,l_n)$, so over a box the robust parametric problem collapses to a problem with known weights. The equality holds only after the maximum over assortments: for a fixed $S$ containing a product with $r_i<\lambda$ the two inner quantities differ.
--
--   **Formalization Note** The inner minimum is a real infimum over the box. The hypotheses $l_0\le u_0$ and $l\le u$ (componentwise) say that each interval is nonempty, the reading of "the interval $[l_i,u_i]$ represents the range of the likely values"; $0<l_0$ and $0<l_i$ express $[l_i,u_i]\subset\mathbb R_{++}$. Revenues are arbitrary reals. Products are 0-indexed (`Fin n`).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, proof of Theorem 3.8, p. 12, second display (outer equality)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_RobustMNL_SizeCon_Model

namespace RobustMNL.SizeCon

/-- Proof of Theorem 3.8, p. 12, second display: over the rectangular set
`∏_{i=0}^n [l_i, u_i] ⊆ ℝⁿ⁺¹₊₊`, for every real `λ`,
`max_{|S| ≤ K} min_{v ∈ V} (1/v₀) ∑_{i ∈ S} v_i (r_i − λ) = max_{|S| ≤ K} (1/u₀) ∑_{i ∈ S} l_i (r_i − λ)`. -/
theorem rectangular_reduction {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hlu₀ : l₀ ≤ u₀) (hl : ∀ i, 0 < l i) (hlu : l ≤ u) (r : Fin n → ℝ) (K : ℕ) (lam : ℝ) :
    paramValue (box l₀ u₀ l u) r K lam =
      (sizeFeasible n K).sup' (sizeFeasible_nonempty n K)
        (fun S => (1 / u₀) * ∑ i ∈ S, l i * (r i - lam)) := by sorry

end RobustMNL.SizeCon
