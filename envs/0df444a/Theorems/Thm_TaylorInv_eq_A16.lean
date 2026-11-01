-- Prove2me | Theorems.Thm_TaylorInv_eq_A16
-- name    : TaylorInv.eq_A16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:18.658423+00:00
-- url     : https://prove2.me/theorems/566d92fe-dc5d-42e7-a236-8bd1c5bac28e
-- title:
--   (A16) — $\sum_j(\underline m-h_0)r_j\ge\frac1\alpha\underline p\,\underline h\,J$
-- statement:
--   Under the standing assumptions and $b_j+h'_j>0$, for almost every feature outcome,
--   $$
--   \sum_{j=1}^J(\underline m-h_0)\,r_j\ \ge\ \frac1\alpha\,\underline p\,\underline h\,J ,
--   $$
--   with $\underline p=\min_jp_j$, $\underline h=\min_jh'_j$ and $\alpha=\max_ju_j/\ell_j$.
--
--   The bound shows that the region $\mathscr A_1$ requires a deviation of order $J$ of the feature sum.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: critical fractile $b_j/(b_j+h'_j)$ → hypothesis $0<b_j+h'_j$; reason: excludes only $b_j=h'_j=0$, where the fractile $0/0$ is undefined
--   - encoding: for (any) feature $x$ in its domain → for almost every outcome $\omega$; reason: Assumption 2's demand range holds for almost every feature outcome; outside a null set the features may leave their range
--   - reading: the chain ending in $=\frac1\alpha\underline p\,\underline hJ$ → the outer inequality $\ge$ only; reason: $\sum_jp_j\min_kb_k\ge J\underline p\,\underline h$ only; e.g. $J=2$, $p_1=1,p_2=2$, $b_j=h'_j=1$ gives $3>2$; the outer inequality is unaffected
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A16), p.OA7

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A16) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA7):
`∑_j (m̲ − h₀) r_j ≥ (1/α) p̲ h̲ J`, for almost every feature outcome, with `p̲ = min_j p_j`,
`h̲ = min_j h′_j` and `α = max_j u_j/ℓ_j`.

**Formalization Note** The page's chain ends with "`= (1/α) p̲ h̲ J`" where only "`≥`" holds; the
outer inequality is stated. `0 < b_j + h′_j` excludes only the undefined critical fractile. -/
theorem eq_A16 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    ∀ᵐ ω ∂μ, 1 / M.α * M.pMin * M.hMin * J ≤ ∑ j, (M.mMin ω - M.h₀) * M.r j ω := by sorry

end TaylorInv
