-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_section_6_2
-- name    : OtterAMM.TwoSided.section_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:56.123389+00:00
-- url     : https://prove2.me/theorems/e16b6831-4c55-412d-a690-790d1cc537c5
-- title:
--   §6.2 — Otter is Pareto optimal for eligible users (both conditions, every profile)
-- statement:
--   Let $F$ satisfy (A1)–(A4) and the selection rule be admissible. For every finite truthful block (each identity a distinct real user reporting its type in $\mathbb R^2_{\ge0}$), the Otter outcome, with final pool input $p_e$ ($Q_Y-M$ if sell-Y dominated, $F^{-1}(-(Q_X-M))$ if sell-X dominated), satisfies:
--
--   (a) no subset of eligible users can reallocate among themselves, each staying within its direction and budget and the subset receiving no outside tokens, so that every member weakly gains and one strictly gains;
--
--   (b) no eligible user can make an additional trade with the pool along $F$ from $p_e$, staying within its direction and budget, that strictly improves its utility.
--
--   The section proves the sell-Y dominated case and states that the other case is symmetric; the statement covers both.
--
--   Differences from the source:
--   - reading: 'no subset of users can trade among themselves (subject to available budgets)' and 'an additional trade directly with the pool' → any reallocation within direction and budget with total net X and net Y not increased (including handing back received tokens), and any signed trade along F from p_e (including unwinding); reason: the paper's own use of Pareto optimality in App. C, Eqs. (53)–(54); the narrower 'sell more unspent budget' reading is weaker. See INSIGHTS.yaml I1: §6.2's proof covers only the narrower reading
--   - reading: final pool position in the sell-X dominated case (by symmetry) → p_e = F⁻¹(−(Q_X − M)) ≤ 0 through Function.invFunOn; reason: the pool receives Q_X − M of X and pays H(Q_X − M) of Y; this is the curve point reached
--   - encoding: utilities of the Pareto comparison → linear utilities x − v·y (sell-Y), y − u·x (sell-X) on positions within direction and budget; reason: on such positions neither catastrophic case of Eq. (2) applies, so this is Eq. (2)
--   - reading: allocation: among welfare maximizers choose one maximizing total sold, then an arbitrary exogenous tie-breaking rule → the statement holds for every selection rule sel with SelRule.Admissible (on every one-sided curve and every finite bid set with nonnegative reports it returns a welfare maximizer of largest total); sel may depend on identity labels; reason: an 'arbitrary exogenous tie-breaking rule' is any choice among the max-total maximizers; such rules exist (continuous welfare on a compact box), so the hypothesis is not vacuous; the §4 priority rule is one instance
--   - encoding: F : (−b_y, +∞) → (−∞, x0) → F : ℝ → ℝ inside the structure PricingCurve, every assumption (A1)–(A4) and the codomain bound imposed on (−b, +∞) only; H(x) = −F⁻¹(−x) through Function.invFunOn on (−b, +∞); reason: Lean functions are total; values outside the domain are never used, so no instance changes
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: reports and types are in ℝ²≥0 (§2) → nonnegativity of asks and budgets is a hypothesis on the identities that occur (ValidOn); reason: the paper's domain of reports, not an extra condition
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), pp. 21–22, §6.2 (PDF 23–24)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG
import Definitions.Def_OtterAMM_TwoSided_Otter
import Definitions.Def_OtterAMM_TwoSided_Properties

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- §6.2 (pp. 21–22): Otter is Pareto optimal for eligible users, (a) among themselves and
(b) against a trade with the pool at the final pool position, in every profile. -/
theorem section_6_2 (C : PricingCurve) (sel : SelRule) (hsel : sel.Admissible) :
    ParetoEligible C (otter C sel) (poolInput C sel) := by sorry

end OtterAMM.TwoSided
