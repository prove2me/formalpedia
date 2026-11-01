-- Prove2me | Theorems.Thm_TaylorInv_eq_A3
-- name    : TaylorInv.eq_A3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:18.743923+00:00
-- url     : https://prove2.me/theorems/ab50a89f-9f2d-4f64-968e-e9e0cea50c38
-- title:
--   (A3) — quadratic upper bound on the retailers' total cost
-- statement:
--   Under the standing assumptions and $b_j+h'_j>0$, for every feature outcome and every allocation $z=(z_1,\dots,z_J)$,
--   $$
--   \sum_{j=1}^JC_j(z_j\mid x_j)\le\sum_{j=1}^J\Big[C_j(s_j^l\mid x_j)-h_0(z_j-s_j^l)+\frac{(z_j-s_j^l)^2}2(b_j+h'_j)u_j\Big],
--   $$
--   where $C_j$ is the retailer cost (4).
--
--   This upper bound is how the cost of the TA allocation is compared with the AF cost on $\mathscr A_2$.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
--   - generalization: the bound at the Taylor allocation $\tilde z$ → the bound for every $z\in\mathbb R^J$; reason: the page's derivation (A2)–(A3) uses no property of $\tilde z$; specializes to $z=\tilde z$
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A3), p.OA3

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A3) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA3): the retailers' total cost is
bounded by its second-order expansion at the local base stocks with the density replaced by its
upper bound `u_j`:
`∑_j C_j(z_j | x_j) ≤ ∑_j [C_j(s_j^l | x_j) − h₀ (z_j − s_j^l) + ((z_j − s_j^l)²/2)(b_j + h′_j) u_j]`.

**Formalization Note** `C_j` is (4) (`retailerCost`). The page states the bound at the Taylor
allocation `z̃`; it is stated here for every `z` and every feature outcome. `0 < b_j + h′_j`
excludes only the undefined critical fractile `0/0`. -/
theorem eq_A3 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    ∀ ω (z : Fin J → ℝ), ∑ j, M.retailerCost j ω (z j) ≤
      ∑ j, (M.retailerCost j ω (M.baseStock j ω) - M.h₀ * (z j - M.baseStock j ω)
        + (z j - M.baseStock j ω) ^ 2 / 2 * (M.b j + M.h' j) * M.u j) := by sorry

end TaylorInv
