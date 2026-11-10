-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_section_6_1
-- name    : OtterAMM.TwoSided.section_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:49.238662+00:00
-- url     : https://prove2.me/theorems/117b241f-fe6f-45e4-84b1-9a0665fa4e5b
-- title:
--   §6.1 — feasibility of Otter in a sell-Y dominated profile: $P_X \le \tilde F^M_Y(Q_Y) = D_X + F(Q_Y-M)$, so $B_X \ge 0$
-- statement:
--   Let $F$ satisfy (A1)–(A4) and the selection rule be admissible. In every sell-Y dominated finite block with reports in $\mathbb R^2_{\ge0}$, with $M=\rho_0D_X$, $Q_Y=\sum_{i\in\mathcal Y}y_i$ and $P_X=\sum_{i\in\mathcal Y}x_i$ (the $X$ paid to sell-Y identities),
--   $$P_X\ \le\ \tilde F^M_Y(Q_Y)\ =\ D_X+F(Q_Y-M),$$
--   so the burnt surplus $B_X:=D_X+F(Q_Y-M)-P_X$ is nonnegative. Together with Fact 8 ($Q_Y\ge M$) this is the sell-Y dominated half of the feasibility clause of Theorem 10.
--
--   Differences from the source:
--   - reading: allocation: among welfare maximizers choose one maximizing total sold, then an arbitrary exogenous tie-breaking rule → the statement holds for every selection rule sel with SelRule.Admissible (on every one-sided curve and every finite bid set with nonnegative reports it returns a welfare maximizer of largest total); sel may depend on identity labels; reason: an 'arbitrary exogenous tie-breaking rule' is any choice among the max-total maximizers; such rules exist (continuous welfare on a compact box), so the hypothesis is not vacuous; the §4 priority rule is one instance
--   - encoding: F : (−b_y, +∞) → (−∞, x0) → F : ℝ → ℝ inside the structure PricingCurve, every assumption (A1)–(A4) and the codomain bound imposed on (−b, +∞) only; H(x) = −F⁻¹(−x) through Function.invFunOn on (−b, +∞); reason: Lean functions are total; values outside the domain are never used, so no instance changes
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: reports and types are in ℝ²≥0 (§2) → nonnegativity of asks and budgets is a hypothesis on the identities that occur (ValidOn); reason: the paper's domain of reports, not an extra condition
--   - encoding: Eq. (8): F̃^M_Y(y) = D_X + F(y − M) for y ≥ M (and H̃^M_X(x) = D_Y + H(x − M)) → curveY C M = spotExtend C.F σ0 M, i.e. σ0·M + F(y − M) (curveX: ρ0·M + H(x − M)); reason: with M = ρ0·D_X one has σ0·M = D_X exactly (σ0·ρ0 = 1), so the curve is the printed one
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 21, §6.1 (PDF 23)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG
import Definitions.Def_OtterAMM_TwoSided_Otter

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- §6.1 (p. 21), feasibility in a sell-Y dominated profile: with `M = ρ0·D_X`,
`Q_Y = Σ_{i∈Y} y_i` and `P_X = Σ_{i∈Y} x_i`, one has `P_X ≤ F̃^M_Y(Q_Y) = D_X + F(Q_Y − M)`,
so the burnt surplus `B_X = D_X + F(Q_Y − M) − P_X` is nonnegative. -/
theorem section_6_1 (C : PricingCurve) (sel : SelRule) (hsel : sel.Admissible)
    (S : Finset Ident) (rep : Ident → Report) (hrep : ValidOn S rep)
    (hdom : SellYDominated C S rep) :
    (∑ i ∈ sellYs S rep, (otter C sel S rep i).1) ≤
        curveY C (C.ρ0 * DX C S rep) (∑ i ∈ sellYs S rep, (otter C sel S rep i).2) ∧
      curveY C (C.ρ0 * DX C S rep) (∑ i ∈ sellYs S rep, (otter C sel S rep i).2) =
        DX C S rep + C.F ((∑ i ∈ sellYs S rep, (otter C sel S rep i).2) - C.ρ0 * DX C S rep) ∧
      0 ≤ DX C S rep + C.F ((∑ i ∈ sellYs S rep, (otter C sel S rep i).2) - C.ρ0 * DX C S rep) -
        (∑ i ∈ sellYs S rep, (otter C sel S rep i).1) := by sorry

end OtterAMM.TwoSided
