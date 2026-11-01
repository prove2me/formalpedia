-- Prove2me | Theorems.Thm_TaylorInv_base_stock_lower_bound
-- name    : TaylorInv.base_stock_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:29.588987+00:00
-- url     : https://prove2.me/theorems/27e9b586-97d9-4607-97e2-25acadc99df5
-- title:
--   Proof of Theorem 1, p.OA7 — $s_j^l\ge b_jp_j$
-- statement:
--   Under the standing assumptions and $b_j+h'_j>0$, for almost every feature outcome and every retailer $j$,
--   $$
--   s_j^l\ \ge\ \frac{b_j}{(b_j+h'_j)u_j}=b_jp_j .
--   $$
--
--   The bound keeps the base stocks, and hence $\underline m$, away from zero; it feeds (A16).
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
--   - encoding: for (any) feature $x$ in its domain → for almost every outcome $\omega$; reason: Assumption 2's demand range holds for almost every feature outcome; outside a null set the features may leave their range
--   - reading: the chain through $F_j^{-1}(0\mid x_j)=0$ → only the conclusion $s_j^l\ge b_jp_j$; reason: the demand support starts at $D\ge0$, not necessarily at $0$; the conclusion holds since $F_j^{-1}(0\mid x_j)\ge0$
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, proof of Theorem 1, display after (A15), p.OA7

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- The lower bound on the local base stock (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023),
proof of Theorem 1, display after (A15), p.OA7): `s_j^l ≥ b_j/((b_j + h′_j) u_j) = b_j p_j`, for
almost every feature outcome.

**Formalization Note** The page's middle steps read `F_j^{-1}(0 | x_j) = 0`; only the conclusion
is stated. `0 < b_j + h′_j` excludes only the undefined critical fractile `0/0`. -/
theorem base_stock_lower_bound {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    ∀ᵐ ω ∂μ, ∀ j, M.b j * M.pc j ≤ M.baseStock j ω := by sorry

end TaylorInv
