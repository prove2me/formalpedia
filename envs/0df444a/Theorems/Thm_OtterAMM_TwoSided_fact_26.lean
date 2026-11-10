-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_fact_26
-- name    : OtterAMM.TwoSided.fact_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:09.018168+00:00
-- url     : https://prove2.me/theorems/125032c6-d937-4823-8986-af71363d6b83
-- title:
--   Fact 26 — for an order-insensitive mechanism, UIC ⇔ strategy-proofness for the builder(-as-user)
-- statement:
--   For every deterministic mechanism on ordered blocks that treats the input bids as an unordered set (its outcome is invariant under permuting the block) and every prescribed ordering $\pi$,
--   $$\text{UIC}\iff\text{strategy-proofness for the builder(-as-user)}.$$
--   Otter is such a mechanism, which is how §6.3 reduces the builder clauses of Theorem 10 to UIC.
--
--   Differences from the source:
--   - encoding: a deterministic AMM mechanism that pays no builder fee and does not observe bid ownership → Mechanism := List Ident → (Ident → Report) → Outcome (ordered labels and reports in, outcome out); utilities of users and builders are Eq. (2) only; reason: ownership is not an input, and with no fee the builder's utility is its Eq. (2) utility
--   - reading: 'order the bids in the prescribed manner'; in UIC the user does not choose the order → a prescribed ordering π (any rule listing each identity of the block once) is a parameter; UIC evaluates both executions in the prescribed order; the builder may use any order of the uncensored block; reason: the paper leaves the prescribed manner abstract; the facts hold for every π
--   - reading: 'strategy-proofness for the builder(-as-user)' → BuilderAsUserSP over every true type in ℝ²≥0, including zero budgets; reason: a builder without intrinsic demand is the zero-budget builder-as-user, as in Fact 27 (App. A); the separate no-bid benchmark is stated in the goal (BuilderSP)
--   - encoding: 'treats the input bids as an unordered set' → OrderInsensitive: the outcome is equal on any two permutations of the block; reason: blocks list each identity once, so permutations are exactly the orders of the same set
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: utility Eq. (2) with value −∞ → util in EReal, −∞ = ⊥; no EReal arithmetic is performed; reason: keeps −∞ a genuine outcome, never a junk real value
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 34, Fact 26 (PDF 36)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_Properties

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Fact 26 (p. 34): if the mechanism treats the input bids as an unordered set, UIC and
strategy-proofness for the builder(-as-user) are equivalent. -/
theorem fact_26 (mech : Mechanism) (π : OrderRule) (hπ : π.Admissible)
    (hord : OrderInsensitive mech) :
    UIC mech π ↔ BuilderAsUserSP mech π := by sorry

end OtterAMM.TwoSided
