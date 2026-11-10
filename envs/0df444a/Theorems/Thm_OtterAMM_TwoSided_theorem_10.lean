-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_theorem_10
-- name    : OtterAMM.TwoSided.theorem_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:56.00483+00:00
-- url     : https://prove2.me/theorems/b163c18f-6630-452f-bd25-c8d55d723f25
-- title:
--   Theorem 10 — main theorem: Otter is well-formed, IR, feasible, UIC, builder(-as-user) strategy-proof and Pareto optimal for eligible users
-- statement:
--   Let the pricing curve $F:(-b,+\infty)\to(-\infty,x_0)$ satisfy (A1)–(A4) ($x_0,y_0>0$, $0<b\le y_0$), let the one-sided VCG auctions use any admissible selection rule (a welfare maximizer of largest total, then an arbitrary tie-breaking), and let $\pi$ be any prescribed ordering of blocks. Then the full two-sided Otter mechanism of §3.2 (both dominance regimes) is
--
--   1. **well-formed**: sell-Y $0\le y_i\le\tilde q_i$, $0\le x_i\le\sigma_0y_i$; sell-X $0\le x_j\le\tilde r_j$, $0\le y_j\le\rho_0x_j$;
--   2. **individually rational**: every truthful user's utility (2) is $\ge0$;
--   3. **feasible**: there are $p\in(-b,+\infty)$ and $B_Y,B_X\ge0$ with $\sum_{\mathcal Y}y_i=\sum_{\mathcal X}y_j+p+B_Y$ and $\sum_{\mathcal X}x_j+F(p)=\sum_{\mathcal Y}x_i+B_X$ (Eq. (41));
--   4. **UIC**: no real user of either direction gains (utility (2), with $-\infty$) by replacing its truthful identity with any finite set of identities with arbitrary nonnegative reports in either direction;
--   5. **strategy-proof for a builder** without intrinsic demand (no injected identities and order of the uncensored block give it positive utility) **and for a builder-as-user** (who may also misreport, inject identities, and order the uncensored block);
--   6. **Pareto optimal for eligible users**: under truthful reporting, (a) no subset of eligible users has a Pareto-improving reallocation among themselves within directions and budgets, and (b) no eligible user has a strictly improving trade with the pool along $F$ from the final pool position.
--
--   Every clause is quantified over all finite blocks with reports in $\mathbb R^2_{\ge0}$.
--
--   Differences from the source:
--   - reading: allocation: among welfare maximizers choose one maximizing total sold, then an arbitrary exogenous tie-breaking rule → the statement holds for every selection rule sel with SelRule.Admissible (on every one-sided curve and every finite bid set with nonnegative reports it returns a welfare maximizer of largest total); sel may depend on identity labels; reason: an 'arbitrary exogenous tie-breaking rule' is any choice among the max-total maximizers; such rules exist (continuous welfare on a compact box), so the hypothesis is not vacuous; the §4 priority rule is one instance
--   - reading: 'order the bids in the prescribed manner'; in UIC the user does not choose the order → a prescribed ordering π (any rule listing each identity of the block once) is a parameter; UIC evaluates both executions in the prescribed order; the builder may use any order of the uncensored block; reason: the paper leaves the prescribed manner abstract; the facts hold for every π
--   - reading: 'well-formed' → WFOutcome: the §2 ranges, nonnegative compensation and the spot-rate caps x ≤ σ0·y (sell-Y), y ≤ ρ0·x (sell-X); reason: the stronger of the readings; Eq. (16) for the dominant side and Eq. (7) for the minority side give the caps
--   - reading: 'feasibility': every token paid is funded by opposite-side orders or an AMM trade, no outside subsidy, surplus burnt → Eq. (41) of App. B: a signed residual pool input p ∈ (−b, +∞) and burns B_Y, B_X ≥ 0; reason: the paper's own formalization of feasibility (App. B)
--   - reading: 'strategy-proofness against a builder(-as-user)' → both BuilderSP (builder with no intrinsic demand, valued as a zero-value zero-budget user of either direction, honest = no bid, utility 0) and BuilderAsUserSP (any true type); reason: covers both roles; the zero-budget valuation of a builder without demand is the paper's in Fact 27
--   - reading: 'Pareto optimality for eligible users': trades among eligible users and with the pool → any reallocation within direction and budget with no outside tokens, and any signed pool trade along F from the final pool input p_e; reason: the paper's own use in App. C, Eqs. (53)–(54); see INSIGHTS.yaml I1
--   - reading: final pool position in the sell-X dominated case → p_e = F⁻¹(−(Q_X − M)); reason: the curve point reached when the pool receives Q_X − M of X
--   - encoding: Eq. (8): F̃^M_Y(y) = D_X + F(y − M) for y ≥ M (and H̃^M_X(x) = D_Y + H(x − M)) → curveY C M = spotExtend C.F σ0 M, i.e. σ0·M + F(y − M) (curveX: ρ0·M + H(x − M)); reason: with M = ρ0·D_X one has σ0·M = D_X exactly (σ0·ρ0 = 1), so the curve is the printed one
--   - encoding: F : (−b_y, +∞) → (−∞, x0) → F : ℝ → ℝ inside the structure PricingCurve, every assumption (A1)–(A4) and the codomain bound imposed on (−b, +∞) only; H(x) = −F⁻¹(−x) through Function.invFunOn on (−b, +∞); reason: Lean functions are total; values outside the domain are never used, so no instance changes
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: utility Eq. (2) with value −∞ → util in EReal, −∞ = ⊥; no EReal arithmetic is performed; reason: keeps −∞ a genuine outcome, never a junk real value
--   - encoding: reports and types are in ℝ²≥0 (§2) → nonnegativity of asks and budgets is a hypothesis on the identities that occur (ValidOn); reason: the paper's domain of reports, not an extra condition
--   - encoding: Otter on an ordered block → otterMech ℓ = otter ℓ.toFinset; well-formedness, IR, feasibility and Pareto are stated for the unordered otter on every finite block; reason: Otter treats the block as a set, so the ordered and unordered statements coincide
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 12, Theorem 10 (PDF 14)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG
import Definitions.Def_OtterAMM_TwoSided_Otter
import Definitions.Def_OtterAMM_TwoSided_Properties

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Theorem 10 (p. 12), main theorem: for every pricing curve satisfying (A1)–(A4), every
selection rule returning a welfare maximizer of largest total, and every prescribed ordering of
blocks, the two-sided Otter mechanism is well-formed, individually rational, feasible, UIC,
strategy-proof for a builder and for a builder-as-user, and Pareto optimal for eligible users. -/
theorem theorem_10 (C : PricingCurve) (sel : SelRule) (hsel : sel.Admissible)
    (π : OrderRule) (hπ : π.Admissible) :
    WellFormed C (otter C sel) ∧
    IndividuallyRational (otter C sel) ∧
    Feasible C (otter C sel) ∧
    UIC (otterMech C sel) π ∧
    BuilderSP (otterMech C sel) ∧
    BuilderAsUserSP (otterMech C sel) π ∧
    ParetoEligible C (otter C sel) (poolInput C sel) := by sorry

end OtterAMM.TwoSided
