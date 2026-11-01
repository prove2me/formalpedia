-- Prove2me | Theorems.Thm_TaylorInv_af_cost_lower_bound
-- name    : TaylorInv.af_cost_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:25.862562+00:00
-- url     : https://prove2.me/theorems/e35776b9-5287-47ef-9f50-7771ae4a4ef8
-- title:
--   Proof of Theorem 1, p.OA10 (corrected: $\bar\epsilon\to$ half-width of the support) — $C_{AF}(x)$ grows linearly in $J$
-- statement:
--   Under the standing assumptions, for every feature outcome $x$, $C_{AF}(x)$ is the sum of the $J$ newsvendor costs at the local base stocks,
--   $$
--   C_{AF}(x)=\sum_{j=1}^J\mathbb E_{\epsilon_j}\big[h'_j(s_j^l-D_j)^++b_j(D_j-s_j^l)^+\mid x_j\big],
--   $$
--   and
--   $$
--   C_{AF}(x)\ \ge\ \underline h\sum_{j=1}^J\ell_j\Big(\frac{hi_j-lo_j}2\Big)^2 ,
--   $$
--   where $[lo_j,hi_j]$ is the support of $\epsilon_j$ and $\underline h=\min_jh'_j$.
--
--   This is the denominator bound of the relative gap: the optimal cost grows linearly in $J$.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - reading: $C_j$ of (4), whose term $-h_0D_j$ the paper omits in its analysis (p.8) → the period cost (2), which equals (3)–(4) with the term kept; reason: with the term omitted the cost differences are unchanged and $C_{OPT}$ only grows; the paper's own display of $C_{AF}(x)$ on p.OA10 is the (2) form
--   - correction: $C_{AF}(x)\ge\underline h\,\underline\ell\,\bar\epsilon^2J$ with $\bar\epsilon$ the bound of Assumption 2 → $C_{AF}(x)\ge\underline h\sum_j\ell_j((hi_j-lo_j)/2)^2$; reason: the printed bound is false when the support is narrower than $[-\bar\epsilon,\bar\epsilon]$: $J=1$, $\epsilon_1$ uniform on $[-1,1]$, $\bar\epsilon=2$, $\ell_1=1/2$, $h'_1=b_1=1$, $h_0=0$ gives $C_{AF}(x)=1/2<2$; the corrected bound equals the printed one when every support is $[-\bar\epsilon,\bar\epsilon]$ and $\ell_j=\underline\ell$
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, proof of Theorem 1, display after (A27), p.OA10

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- The lower bound on the AF cost, corrected (Huang, Shang, Yang & Zhou, SSRN 3993516
(Jan 29 2023), proof of Theorem 1, p.OA10): for every feature outcome, `C_AF(x)` is the sum of the
`J` newsvendor costs at the local base stocks, and
`C_AF(x) ≥ h̲ ∑_j ℓ_j ((hi_j − lo_j)/2)²`, where `[lo_j, hi_j]` is the support of `ϵ_j`.

**Formalization Note** The page prints `h̲ ℓ̲ ϵ̄² J` with `ϵ̄` the bound of Assumption 2; that is
false when the support of `ϵ_j` is narrower than `[−ϵ̄, ϵ̄]`. The corrected bound uses the half
width of each support and equals the printed one when every support is `[−ϵ̄, ϵ̄]` and
`ℓ_j = ℓ̲`. -/
theorem af_cost_lower_bound {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ) :
    ∀ ω, M.costAFGiven ω = ∑ j, M.newsvendor j ω (M.baseStock j ω) ∧
      M.hMin * ∑ j, M.ℓ j * ((M.hi j - M.lo j) / 2) ^ 2 ≤ M.costAFGiven ω := by sorry

end TaylorInv
