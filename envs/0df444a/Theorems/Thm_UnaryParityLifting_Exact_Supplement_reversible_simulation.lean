-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_reversible_simulation
-- name    : UnaryParityLifting.Exact.Supplement.reversible_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:08.176208+00:00
-- url     : https://prove2.me/theorems/2416d2bb-f020-4e9a-91ad-9f1a023ec3c4
-- title:
--   Proposition 7.3 — Linear simulation by unary parity certificates
-- statement:
--   There is one absolute C>0 such that, for every finite variable set V, ordinary source CNF F and RevRes(⊕) refutation p of F, an actual uSA(⊕) certificate q of F exists with
--
--   $$s(q)\le C\operatorname{size}(p).$$
--
--   Every axiom multiplier of q is a nonnegative integer constant and every conical parity weight is a nonnegative integer. Both sides use matched explicit clause serialization; size includes initial occurrences and rule applications, not just the number of steps or maximum configuration size. The overhead constant is quantified before the variable set, formula and proof. This is the simulation used for the Tseitin upper bound in incomparability.
--
--   Differences from the source:
--   - encoding: O(S) with the source written-occurrence encoding → one uniform positive linear constant and a fixed matched binary charge; reason: each final occurrence is charged to an initial occurrence or its last production as on p.21, so the constant is independent of dimension and proof
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.21, Proposition 7.3

import Definitions.Def_UnaryParityLifting_Exact_Supplement_reversible

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Proposition 7.3: one absolute linear written-size overhead. -/
theorem reversible_simulation :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (F : LiftSAParity.CNF V)
      (p : RevProof V), SourceCNF F → p.Refutes F →
      ∃ q : CertificateSyntax F, q.Valid ∧ ConstantParity q ∧
        (chargedSize (binaryCharge V) q : ℝ) ≤ C * p.size := by sorry

end UnaryParityLifting.Exact.Supplement
