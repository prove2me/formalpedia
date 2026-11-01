-- Prove2me | Theorems.Thm_TaylorInv_eq_A19
-- name    : TaylorInv.eq_A19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:40.505781+00:00
-- url     : https://prove2.me/theorems/315deea4-3487-4983-af8f-fbb7132587ed
-- title:
--   (A19) — $\mathbb P(x\in\mathscr A_1)$ is exponentially small
-- statement:
--   Under the standing assumptions and $b_j+h'_j>0$,
--   $$
--   \mathbb P(x\in\mathscr A_1)\le\mathbb P\Big(\Big|\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb Ex_{jp})\Big|\ge\frac1\alpha\underline p\,\underline hJ\Big)\le2\exp\Big(-\frac{\underline p^2\underline h^2J}{2\alpha^2P\bar M^2\bar B^2}\Big).
--   $$
--
--   On $\mathscr A_1$ the TA order is too small to give every retailer a positive allocation; this bound makes that event negligible.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: $\mathbb E x_{jp}=0$ without loss of generality (p.OA6) and the sum $\sum_j\sum_p\beta_{jp}x_{jp}$ → the centred sum $\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb E x_{jp})$; reason: the paper's own recentring of the features (p.OA6); the statement is the same after it
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A19), p.OA8

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A19) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA8):
`ℙ(x ∈ 𝒜₁) ≤ ℙ(|∑_j ∑_p β_jp x_jp| ≥ (1/α) p̲ h̲ J) ≤ 2 exp(−p̲² h̲² J/(2 α² P M̄² B̄²))`.

**Formalization Note** The feature sum is centred (`centredSum`), replacing the paper's
`𝔼 x_jp = 0` (p.OA6). `0 < b_j + h′_j` excludes only the undefined critical fractile. -/
theorem eq_A19 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    μ (M.region1 μ) ≤ μ {ω | 1 / M.α * M.pMin * M.hMin * J ≤ |M.centredSum μ ω|} ∧
      μ {ω | 1 / M.α * M.pMin * M.hMin * J ≤ |M.centredSum μ ω|}
        ≤ ENNReal.ofReal (2 * Real.exp (-(M.pMin ^ 2 * M.hMin ^ 2 * J)
            / (2 * M.α ^ 2 * P * Mbar ^ 2 * Bbar ^ 2))) := by sorry

end TaylorInv
