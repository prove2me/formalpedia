-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_endpoint_identity
-- name    : UnaryParityLifting.Exact.Supplement.endpoint_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:50:18.78774+00:00
-- url     : https://prove2.me/theorems/5f58fb8e-4ae6-4ce7-b53f-c1333bbdb3d2
-- title:
--   Proposition 7.2 — Static endpoint identity
-- statement:
--   Let F be a finite ordinary CNF with tautologies omitted, viewed as parity clauses. Let p be any valid reversible parity derivation whose initial multiset has α_C copies of C for each C∈F, where α_C is any natural multiplicity. Suppose its final multiset consists of q≥1 copies of the empty clause and a multiset B of further parity-clause occurrences. Then, for every Boolean assignment x,
--
--   $$\sum_{C\in F}\alpha_C\bar C(x)=q+\sum_{D\in B}\bar D(x).$$
--
--   Bars are falsification indicators. The multiset sum retains every final occurrence, even if several clauses agree syntactically or semantically; q is not fixed to one. The identity is the static interface used to convert reversible proofs to unary certificates.
--
--   Differences from the source:
--   - encoding: indexed clauses and final clause occurrences → finite clause subtypes and a final multiset; reason: this replaces indexing without changing multiplicities, q, or pointwise equality
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.21, Proposition 7.2

import Definitions.Def_UnaryParityLifting_Exact_Supplement_reversible

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Proposition 7.2: arbitrary multiplicities, q copies of bottom and every remaining occurrence. -/
theorem endpoint_identity {V : Type} [Fintype V] (F : LiftSAParity.CNF V)
    (hF : SourceCNF F) (α : {C // C ∈ F} → ℕ) (p : RevProof V) (q : ℕ) (B : Multiset (ParityClause V))
    (hp : p.Valid) (hq : 1 ≤ q)
    (hi : p.initial = ∑ C : {C // C ∈ F}, Multiset.replicate (α C) (ordinaryParity C.val))
    (hf : p.final = Multiset.replicate q [] + B) :
    ∀ x : V → Bool,
      (∑ C : {C // C ∈ F}, (α C : ℝ) * clauseIndicator C.val x) =
        (q : ℝ) + (B.map (fun D => parityIndicator D x)).sum := by sorry

end UnaryParityLifting.Exact.Supplement
