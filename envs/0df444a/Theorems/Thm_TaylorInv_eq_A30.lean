-- Prove2me | Theorems.Thm_TaylorInv_eq_A30
-- name    : TaylorInv.eq_A30
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:43.876996+00:00
-- url     : https://prove2.me/theorems/eb873df3-ec5e-405e-a1b4-4a4c3f4253b8
-- title:
--   (A30) — $|C_{TA}(x)-C_{AF}(x)|$ on $\mathscr A_2$
-- statement:
--   Under the standing assumptions and $b_j+h'_j>0$, for almost every feature outcome $x\in\mathscr A_2$, with $S(x)=\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb Ex_{jp})$,
--   $$
--   |C_{TA}(x)-C_{AF}(x)|\le2h_0|S(x)|+\frac{\alpha^3}{2\underline tJ}|S(x)|^2 .
--   $$
--
--   This pathwise bound gives the high-probability rates of Theorem 1(ii).
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - reading: $C_j$ of (4), whose term $-h_0D_j$ the paper omits in its analysis (p.8) → the period cost (2), which equals (3)–(4) with the term kept; reason: with the term omitted the cost differences are unchanged and $C_{OPT}$ only grows; the paper's own display of $C_{AF}(x)$ on p.OA10 is the (2) form
--   - encoding: $\mathbb E x_{jp}=0$ without loss of generality (p.OA6) and the sum $\sum_j\sum_p\beta_{jp}x_{jp}$ → the centred sum $\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb E x_{jp})$; reason: the paper's own recentring of the features (p.OA6); the statement is the same after it
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
--   - encoding: for (any) feature $x$ in its domain → for almost every outcome $\omega$; reason: Assumption 2's demand range holds for almost every feature outcome; outside a null set the features may leave their range
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A30), p.OA11

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A30) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA11): for `x ∈ 𝒜₂`,
`|C_TA(x) − C_AF(x)| ≤ 2 h₀ |∑_j ∑_p β_jp x_jp| + (α³/(2 t̲ J)) |∑_j ∑_p β_jp x_jp|²`, for almost
every feature outcome.

**Formalization Note** The feature sum is centred (`centredSum`), replacing the paper's
`𝔼 x_jp = 0` (p.OA6). `0 < b_j + h′_j` excludes only the undefined critical fractile. -/
theorem eq_A30 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    ∀ᵐ ω ∂μ, ω ∈ M.region2 μ →
      |M.costTAGiven μ ω - M.costAFGiven ω|
        ≤ 2 * M.h₀ * |M.centredSum μ ω| + M.α ^ 3 / (2 * M.tMin * J) * |M.centredSum μ ω| ^ 2 := by sorry

end TaylorInv
