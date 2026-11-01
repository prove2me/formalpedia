-- Prove2me | Theorems.Thm_TaylorInv_eq_A25
-- name    : TaylorInv.eq_A25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:27.918695+00:00
-- url     : https://prove2.me/theorems/6cad5597-9a6c-4746-8d8b-9dffc4ca7e30
-- title:
--   (A25) — the quadratic allocation error on $\mathscr A_2$ is $O(1)$
-- statement:
--   Under the standing assumptions, $b_j+h'_j>0$ and $J\ge1$, with $\tilde z_j=\tilde z_j(\tilde z_0,x)$ the TA allocation,
--   $$
--   \mathbb E\Big[\mathbf 1_{\mathscr A_2}\sum_{j=1}^J\frac{(\tilde z_j-s_j^l)^2}{2p_j}\Big]\le\frac{\alpha^3}{2\underline tJ}\sum_{j=1}^J\sum_{p=1}^P\beta_{jp}^2\,\mathrm{Var}(x_{jp})\le\frac{\alpha^3P\bar B^2\bar\sigma^2}{2\underline t}.
--   $$
--
--   This is the $O(1)$ term of $C_{TA}-C_{AF}$: on $\mathscr A_2$ the allocation error is spread over all retailers.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
--   - encoding: $\mathbb E_{x\in\mathscr A_2}[\cdot]$ → $\int_{\mathscr A_2}\cdot\,d\mu$; reason: the three regional terms of (A13) add up to the expectation over all features, so $\mathbb E_{x\in\mathscr A_i}$ is the restricted integral
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A25), p.OA9

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A25) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA9): for `J ≥ 1`,
`𝔼_{x∈𝒜₂}[∑_j (z̃_j − s_j^l)²/(2 p_j)] ≤ (α³/(2 t̲ J)) ∑_j ∑_p β_jp² Var(x_jp) ≤ α³ P B̄² σ̄²/(2 t̲)`,
where `z̃ = z̃(z̃₀, x)` is the TA allocation and `𝔼_{x∈𝒜₂}[Y] = 𝔼[Y; 𝒜₂]`.

**Formalization Note** `𝔼_{x∈𝒜₂}` is the integral over `𝒜₂` (the three regional terms of (A13)
add up to the expectation over all features). `0 < b_j + h′_j` excludes only the undefined critical
fractile. -/
theorem eq_A25 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) (hJ : 1 ≤ J) :
    ∫ ω in M.region2 μ, ∑ j, (M.taAlloc (M.taOrder μ) ω j - M.baseStock j ω) ^ 2 / (2 * M.pc j) ∂μ
        ≤ M.α ^ 3 / (2 * M.tMin * J) * ∑ j, ∑ p, M.β j p ^ 2 * variance (M.X j p) μ ∧
      M.α ^ 3 / (2 * M.tMin * J) * ∑ j, ∑ p, M.β j p ^ 2 * variance (M.X j p) μ
        ≤ M.α ^ 3 * P * Bbar ^ 2 * σbar ^ 2 / (2 * M.tMin) := by sorry

end TaylorInv
