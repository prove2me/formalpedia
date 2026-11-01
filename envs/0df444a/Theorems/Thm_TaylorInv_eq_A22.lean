-- Prove2me | Theorems.Thm_TaylorInv_eq_A22
-- name    : TaylorInv.eq_A22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:29.531322+00:00
-- url     : https://prove2.me/theorems/2dbdafaa-f607-493d-b668-a99e7e6082e6
-- title:
--   (A22) (corrected: $\underline h\to h_0$ in the exponent) — $\mathbb P(x\in\mathscr A_3)$ is exponentially small
-- statement:
--   Under the standing assumptions and $b_j+h'_j>0$,
--   $$
--   \mathbb P(x\in\mathscr A_3)\le\mathbb P\Big(\Big|\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb Ex_{jp})\Big|\ge\underline p\,h_0J\Big)\le2\exp\Big(-\frac{\underline p^2h_0^2J}{2\alpha^2P\bar M^2\bar B^2}\Big).
--   $$
--
--   On $\mathscr A_3$ the TA order covers every approximate echelon base stock; the bound controls this region when $h_0>0$.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: $\mathbb E x_{jp}=0$ without loss of generality (p.OA6) and the sum $\sum_j\sum_p\beta_{jp}x_{jp}$ → the centred sum $\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb E x_{jp})$; reason: the paper's own recentring of the features (p.OA6); the statement is the same after it
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
--   - correction: final exponent $-\underline p^2\underline h^2J/(2\alpha^2P\bar M^2\bar B^2)$ → $-\underline p^2h_0^2J/(2\alpha^2P\bar M^2\bar B^2)$; reason: the printed bound is false when $h_0<\underline h$: with $J\ge5$, $P=1$, $x_j$ uniform on $\{\pm1\}$, $\beta_j=1$, $\gamma_j=2$, $\epsilon_j$ uniform on $[-1,1]$, $h_0=0$, $h'_j=b_j=1$, $\mathscr A_3=\{\sum_jx_j\le0\}$ has probability $\ge1/2>2e^{-J/2}$; the page's own previous line $\underline ph_0J$ gives $h_0$
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A22), p.OA8

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A22), corrected (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA8):
`ℙ(x ∈ 𝒜₃) ≤ ℙ(|∑_j ∑_p β_jp x_jp| ≥ p̲ h₀ J) ≤ 2 exp(−p̲² h₀² J/(2 α² P M̄² B̄²))`.

**Formalization Note** The page prints `h̲` in the final exponent; its own previous line has
`p̲ h₀ J`, which gives `h₀`, and the printed bound is false when `h₀ < h̲`. The feature sum is
centred (`centredSum`). `0 < b_j + h′_j` excludes only the undefined critical fractile. -/
theorem eq_A22 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    μ (M.region3 μ) ≤ μ {ω | M.pMin * M.h₀ * J ≤ |M.centredSum μ ω|} ∧
      μ {ω | M.pMin * M.h₀ * J ≤ |M.centredSum μ ω|}
        ≤ ENNReal.ofReal (2 * Real.exp (-(M.pMin ^ 2 * M.h₀ ^ 2 * J)
            / (2 * M.α ^ 2 * P * Mbar ^ 2 * Bbar ^ 2))) := by sorry

end TaylorInv
