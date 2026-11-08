-- Prove2me | Theorems.Thm_TaylorInv_eq_18
-- name    : TaylorInv.eq_18
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:32:29.622829+00:00
-- url     : https://prove2.me/theorems/98182d48-016f-43c5-854a-3aa7639cf1b6
-- title:
--   Eq. (18) — the local base stock is linear in the features
-- statement:
--   Assume the model's standing assumptions and $b_j+h'_j>0$. For every retailer $j$ and every feature outcome,
--   $$
--   s_j^l=F_j^{-1}\Big(\frac{b_j}{b_j+h'_j}\,\Big|\,x_j\Big)=\beta_{j0}+\sum_{p=1}^P\beta_{jp}x_{jp},\qquad \beta_{j0}=\gamma_j+F_{\epsilon_j}^{-1}\Big(\frac{b_j}{b_j+h'_j}\Big).
--   $$
--
--   This makes the TA order $\tilde z_0$ an explicit expectation and turns the deviation $\sum_js_j^l-\tilde z_0$ into a centred linear function of the features.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: retailers $j\in[J]^+$ and features $p\in[P]^+$ → `Fin J` and `Fin P` (0-based); reason: Lean convention; same instances
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (18), p.14

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- Eq. (18) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.14): under the linear demand
model the local base stock is linear in the features,
`s_j^l = F_j^{-1}(b_j/(b_j + h′_j) | x_j) = β_j0 + ∑_p β_jp x_jp` with
`β_j0 = γ_j + F_{ϵ_j}^{-1}(b_j/(b_j + h′_j))`, for every feature outcome.

**Formalization Note** `0 < b_j + h′_j` excludes only the case `b_j = h′_j = 0`, where the
critical fractile `0/0` is undefined. -/
theorem eq_18 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    ∀ j ω, M.baseStock j ω = (M.γ j + M.noiseQuantile j) + ∑ p, M.β j p * M.X j p ω := by sorry

end TaylorInv
