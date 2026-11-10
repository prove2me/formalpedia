-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_fact_25
-- name    : OtterAMM.TwoSided.fact_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:00.452198+00:00
-- url     : https://prove2.me/theorems/15fa3f1d-7ff4-4c52-9405-f87b189a6c09
-- title:
--   Fact 25 — strategy-proofness for a builder-as-user implies UIC
-- statement:
--   For every deterministic mechanism on ordered blocks (no builder fee; bid ownership unobservable) and every prescribed ordering $\pi$: if the mechanism is strategy-proof for a builder-as-user (a builder with a true type who may misreport, inject any finite set of identities in either direction, and order the whole uncensored block arbitrarily, compared to one truthful identity in the prescribed order), then it is UIC (the same comparison for a user who cannot choose the order).
--
--   Differences from the source:
--   - encoding: a deterministic AMM mechanism that pays no builder fee and does not observe bid ownership → Mechanism := List Ident → (Ident → Report) → Outcome (ordered labels and reports in, outcome out); utilities of users and builders are Eq. (2) only; reason: ownership is not an input, and with no fee the builder's utility is its Eq. (2) utility
--   - reading: 'order the bids in the prescribed manner'; in UIC the user does not choose the order → a prescribed ordering π (any rule listing each identity of the block once) is a parameter; UIC evaluates both executions in the prescribed order; the builder may use any order of the uncensored block; reason: the paper leaves the prescribed manner abstract; the facts hold for every π
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: utility Eq. (2) with value −∞ → util in EReal, −∞ = ⊥; no EReal arithmetic is performed; reason: keeps −∞ a genuine outcome, never a junk real value
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 34, Fact 25 (PDF 36)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_Properties

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Fact 25 (p. 34): for every deterministic mechanism on ordered blocks (no builder fee, bid
ownership unobservable) and every prescribed ordering, strategy-proofness for a builder-as-user
implies UIC. -/
theorem fact_25 (mech : Mechanism) (π : OrderRule) (hπ : π.Admissible) :
    BuilderAsUserSP mech π → UIC mech π := by sorry

end OtterAMM.TwoSided
