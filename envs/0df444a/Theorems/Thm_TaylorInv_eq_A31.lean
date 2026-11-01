-- Prove2me | Theorems.Thm_TaylorInv_eq_A31
-- name    : TaylorInv.eq_A31
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:47.250597+00:00
-- url     : https://prove2.me/theorems/770851a8-69a4-457a-9444-2f7ecfd92240
-- title:
--   (A31) — $\mathbb P(x\in\mathscr A_2)\ge1-2\exp(-\underline p^2h_0^2J/(2\alpha^2P\bar M^2\bar B^2))$
-- statement:
--   Under the standing assumptions and $b_j+h'_j>0$,
--   $$
--   \mathbb P(x\in\mathscr A_2)\ \ge\ 1-2\exp\Big(-\frac{\underline p^2h_0^2J}{2\alpha^2P\bar M^2\bar B^2}\Big).
--   $$
--
--   The middle region, where the Taylor allocation is the proportional rule (15), carries almost all the probability when $h_0>0$.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A31), p.OA12

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A31) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA12):
`ℙ(x ∈ 𝒜₂) ≥ 1 − 2 exp(−p̲² h₀² J/(2 α² P M̄² B̄²))`.

**Formalization Note** The probability is `μ.real` of the region. `0 < b_j + h′_j` excludes only
the undefined critical fractile. -/
theorem eq_A31 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    1 - 2 * Real.exp (-(M.pMin ^ 2 * M.h₀ ^ 2 * J) / (2 * M.α ^ 2 * P * Mbar ^ 2 * Bbar ^ 2))
      ≤ μ.real (M.region2 μ) := by sorry

end TaylorInv
