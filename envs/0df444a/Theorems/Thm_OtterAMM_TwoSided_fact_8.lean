-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_fact_8
-- name    : OtterAMM.TwoSided.fact_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:40.782852+00:00
-- url     : https://prove2.me/theorems/a6076d77-a58d-4041-998c-52f0d52cc844
-- title:
--   Fact 8 — in a sell-Y dominated profile, $Q_Y \ge M$
-- statement:
--   Let $F$ be a pricing curve satisfying (A1)–(A4), let the one-sided VCG auction use an admissible selection rule (a welfare maximizer of largest total), and consider any finite block of reports in $\mathbb R^2_{\ge0}$ that is sell-Y dominated, $D_Y\ge\rho_0D_X$, with $M=\rho_0D_X$. Let $Q_Y=\sum_{i\in\mathcal Y}y_i$ be the aggregate $Y$ spent by the sell-Y identities under Otter. Then
--   $$Q_Y\ \ge\ M.$$
--   This is what makes the minority side's compensation fundable in §6.1.
--
--   Differences from the source:
--   - reading: allocation: among welfare maximizers choose one maximizing total sold, then an arbitrary exogenous tie-breaking rule → the statement holds for every selection rule sel with SelRule.Admissible (on every one-sided curve and every finite bid set with nonnegative reports it returns a welfare maximizer of largest total); sel may depend on identity labels; reason: an 'arbitrary exogenous tie-breaking rule' is any choice among the max-total maximizers; such rules exist (continuous welfare on a compact box), so the hypothesis is not vacuous; the §4 priority rule is one instance
--   - encoding: F : (−b_y, +∞) → (−∞, x0) → F : ℝ → ℝ inside the structure PricingCurve, every assumption (A1)–(A4) and the codomain bound imposed on (−b, +∞) only; H(x) = −F⁻¹(−x) through Function.invFunOn on (−b, +∞); reason: Lean functions are total; values outside the domain are never used, so no instance changes
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: reports and types are in ℝ²≥0 (§2) → nonnegativity of asks and budgets is a hypothesis on the identities that occur (ValidOn); reason: the paper's domain of reports, not an extra condition
--   - encoding: Eq. (8): F̃^M_Y(y) = D_X + F(y − M) for y ≥ M (and H̃^M_X(x) = D_Y + H(x − M)) → curveY C M = spotExtend C.F σ0 M, i.e. σ0·M + F(y − M) (curveX: ρ0·M + H(x − M)); reason: with M = ρ0·D_X one has σ0·M = D_X exactly (σ0·ρ0 = 1), so the curve is the printed one
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 11, Fact 8 (PDF 13)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG
import Definitions.Def_OtterAMM_TwoSided_Otter

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Fact 8 (p. 11): in a sell-Y dominated profile, the aggregate `Y` spent by the sell-Y
identities is at least `M = ρ0·D_X`. -/
theorem fact_8 (C : PricingCurve) (sel : SelRule) (hsel : sel.Admissible)
    (S : Finset Ident) (rep : Ident → Report) (hrep : ValidOn S rep)
    (hdom : SellYDominated C S rep) :
    C.ρ0 * DX C S rep ≤ ∑ i ∈ sellYs S rep, (otter C sel S rep i).2 := by sorry

end OtterAMM.TwoSided
