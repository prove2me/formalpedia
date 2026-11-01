-- Prove2me | Theorems.Thm_TaylorInv_ta_minus_af_bounded
-- name    : TaylorInv.ta_minus_af_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:43.05618+00:00
-- url     : https://prove2.me/theorems/52c538cf-9354-4a92-bc46-e739bbc712fe
-- title:
--   (A27), p.OA10 — $C_{TA}-C_{AF}$ is bounded by a constant
-- statement:
--   Fix $P$ and bounds $0\le h_0\le\underline h\le\bar h\le\bar b$, $0<\underline\ell\le\bar u$, $\bar D,\bar\epsilon,\bar B,\bar M,\bar\sigma$. There is a constant $K$, depending only on these, such that for every $J\ge1$ and every $J$-retailer system in the class,
--   $$
--   C_{TA}-C_{AF}\le K .
--   $$
--
--   Together with $C_{AF}\ge cJ$ this gives the $O(J^{-1})$ relative gap of Theorem 1(i).
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - reading: $C_j$ of (4), whose term $-h_0D_j$ the paper omits in its analysis (p.8) → the period cost (2), which equals (3)–(4) with the term kept; reason: with the term omitted the cost differences are unchanged and $C_{OPT}$ only grows; the paper's own display of $C_{AF}(x)$ on p.OA10 is the (2) form
--   - encoding: retailers $j\in[J]^+$ and features $p\in[P]^+$ → `Fin J` and `Fin P` (0-based); reason: Lean convention; same instances
--   - reading: $C_{TA}-C_{AF}=O(1)$ → $\exists K$ depending only on $P$ and the class bounds, for every $J\ge1$ and every system in the class; reason: the paper calls $\alpha,\underline p,\underline t,\bar t,\underline h,\bar h,\bar b,\bar D$ constants; uniformity over $J$ is the content of $O(1)$
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, proof of Theorem 1, (A27) and the sentence after it, p.OA10

import Mathlib
import Definitions.Def_TaylorInv_Policies
import Definitions.Def_TaylorInv_InClass

open MeasureTheory ProbabilityTheory

universe u

namespace TaylorInv

/-- `C_TA − C_AF = O(1)` (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), proof of
Theorem 1, after (A27), p.OA10: "which shows that `C_TA − C_AF` can be bounded by a constant").
Fix `P` and the bounds of `Model.InClass`; there is a constant `K`, depending only on these, with
`C_TA − C_AF ≤ K` for every `J ≥ 1` and every system in the class.

**Formalization Note** "`O(1)`" is a constant uniform in `J` and in the systems of the class. The
correction `0 < h̲` of Theorem 1 is not assumed here: the paper states this bound under its own cost
order `0 ≤ h₀ ≤ h̲`, and at `h̲ = 0` (where `h₀ = 0`) the bound still holds, though the paper's
explicit constant (A27) then does not apply. -/
theorem ta_minus_af_bounded (P : ℕ) (h₀ hlow hbar bbar ℓlow ubar Dbar ϵbar Bbar Mbar σbar : ℝ)
    (hh₀ : 0 ≤ h₀) (hh₀low : h₀ ≤ hlow) (hlowbar : hlow ≤ hbar)
    (hbarb : hbar ≤ bbar) (hℓlow : 0 < ℓlow) (hℓu : ℓlow ≤ ubar) :
    ∃ K : ℝ, ∀ (J : ℕ), 1 ≤ J → ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (M : Model J P Ω),
      M.InClass μ h₀ hlow hbar bbar ℓlow ubar Dbar ϵbar Bbar Mbar σbar →
      M.costTA μ - M.costAF μ ≤ K := by sorry

end TaylorInv
