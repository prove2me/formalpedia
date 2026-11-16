-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_integer_rounding
-- name    : UnaryParityLifting.Exact.Supplement.integer_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:11.348318+00:00
-- url     : https://prove2.me/theorems/8bc10ddc-e01a-4b28-8b6a-c9dd6f69e2c7
-- title:
--   Lemma A.1 — Integer rounding of an arbitrary exact certificate
-- statement:
--   Let F be a source CNF on N variables and 1≤d≤N. Let q be any exact real certificate with nonnegative constant axiom multipliers and nonnegative collected conical weights, of termwise degree≤d. Write W=W(q) for the sum of all coefficients and M≥1 for the actual number of nonzero axiom and conical coefficients after collection. An exact integer certificate q′ exists, again with nonnegative constant axiom multipliers and degree≤d, with
--
--   $$W(q')\le3\cdot4^d M(W+1).$$
--
--   The output has natural-number coefficients on both sides and is a formal polynomial identity, so no Boolean-axiom multipliers are needed. The assertion covers arbitrary such real certificates, not only the lifted certificates. It is the independent rounding interface used by Theorem A.2.
--
--   Differences from the source:
--   - encoding: W and M defined in the sentence; integer nonnegative constants → mass and nonzero count computed from the published certificate, with explicit natural-number witnesses for integrality; reason: identical terms and clauses are already collected and both axiom and conical coefficients are counted
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.24, Lemma A.1

import Definitions.Def_UnaryParityLifting_Exact_Supplement_integerOutput

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Lemma A.1: arbitrary exact real certificates and collected coefficient count. -/
theorem integer_rounding (N d : ℕ) (F : LiftSAParity.CNF (Fin N))
    (hF : SourceCNF F) (hd : 1 ≤ d) (hdN : d ≤ N) (q : RealCertificate F)
    (he : q.IsExact) (hdeg : q.DegreeLE d) (hM : 1 ≤ coefficientCount q) :
    ∃ q' : RealCertificate F, q'.IsExact ∧ IntegerOutput q' ∧ q'.DegreeLE d ∧
      q'.mass ≤ 3 * (4 : ℝ) ^ d * coefficientCount q * (q.mass + 1) := by sorry

end UnaryParityLifting.Exact.Supplement
