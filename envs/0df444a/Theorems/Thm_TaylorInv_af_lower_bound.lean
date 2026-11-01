-- Prove2me | Theorems.Thm_TaylorInv_af_lower_bound
-- name    : TaylorInv.af_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:10.136314+00:00
-- url     : https://prove2.me/theorems/b2c65fe7-cc07-4a7a-a10d-ed71c10d66da
-- title:
--   Proof of Theorem 1 (i), p.OA5 — the AF system lower-bounds OPT
-- statement:
--   Under the standing assumptions, for every feature outcome $x$, every order $z_0\ge0$ and every feasible allocation $z$,
--   $$
--   C_{AF}(x)\le h_0\Big(z_0-\sum_jz_j\Big)+\sum_jN_j(z_j\mid x).
--   $$
--   Consequently $C_{AF}(x)\le h_0z_0+G(z_0\mid x)$ for every $z_0\ge0$, in particular $C_{AF}(x)\le C_{OPT}(x)$, and
--   $$
--   C_{AF}\le C_{OPT}.
--   $$
--
--   The advanced-feature system, which sees $x$ before ordering, is the benchmark against which the TA policy is measured.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - reading: $C_j$ of (4), whose term $-h_0D_j$ the paper omits in its analysis (p.8) → the period cost (2), which equals (3)–(4) with the term kept; reason: with the term omitted the cost differences are unchanged and $C_{OPT}$ only grows; the paper's own display of $C_{AF}(x)$ on p.OA10 is the (2) form
--   - encoding: $z_j>0$, $z_0>0$ in (5) and (14) → $z_j\ge0$, $z_0\ge0$; reason: (6) uses $z_j\ge0$; the argmin of (14) has zero coordinates in case (16); the infimum (5) is unchanged
--   - encoding: $\tilde z(z_0,x)=\arg\min$ of (14), $C_{OPT}=\min_{z_0}$ → `Classical.epsilon` choice of a minimizer; $C_{OPT}$ as an infimum over $z_0\ge0$; reason: the minimizer of (14) is unique (Proposition 2); the infimum equals the minimum when it is attained
--   - generalization: $C_{AF}(x)\le C_{OPT}(x)$ at the optimal order $z_0^*$ → the bound at every order $z_0\ge0$ and every feasible allocation; reason: specializes to $z_0=z_0^*$; needs no existence of $z_0^*$
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, proof of Theorem 1 (i), p.OA5

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- The advanced-feature lower bound (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), proof
of Theorem 1 (i), p.OA5): for every feature outcome, the AF solution `z_j^AF = s_j^l`,
`z₀^AF = ∑_j s_j^l` minimizes the period cost over all orders `z₀ ≥ 0` and feasible allocations, so
`C_AF(x) ≤ C_OPT(x)`, and `C_AF ≤ C_OPT`.

**Formalization Note** `optCostGiven z₀ ω` is `h₀ z₀ + G(z₀ | x)`; the bound is stated at every order
`z₀ ≥ 0`, which includes the optimal order `z₀*`. -/
theorem af_lower_bound {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ) :
    (∀ ω, ∀ z₀, 0 ≤ z₀ → ∀ z ∈ feasible z₀, M.costAFGiven ω ≤ M.cost z₀ z ω) ∧
    (∀ ω, ∀ z₀, 0 ≤ z₀ → M.costAFGiven ω ≤ M.optCostGiven z₀ ω) ∧
    M.costAF μ ≤ M.costOPT μ := by sorry

end TaylorInv
