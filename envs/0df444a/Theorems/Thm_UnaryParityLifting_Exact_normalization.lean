-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_normalization
-- name    : UnaryParityLifting.Exact.normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:56.57921+00:00
-- url     : https://prove2.me/theorems/57cc5034-f45b-48b3-960c-5b20f4599995
-- title:
--   Lemma 2.4 — Normalization
-- statement:
--   Let $H$ be a CNF on $v$ Boolean variables with no tautological clause. Let $S$ bound the charged size of an integer uSA(⊕) certificate in the explicit encoding. Empty clauses and nonsquarefree input monomials are allowed. There are nonnegative integers $a_C,b_j$ and parity clauses $D_j$ such that, on the whole cube,
--   $$\sum_{C\in H}a_C\overline C=1+\sum_jb_j\overline D_j,$$
--   $$\sum_Ca_C\le S,\qquad\sum_Ca_C+\sum_jb_j\le(v+2)S,\qquad|\{C:a_C\ne0\}|\le S.$$
--
--   Bars denote falsification. Zero RHS weights are omitted from the written list. This gives a constant-multiplier identity with both mass and axiom support controlled; normalization is a conclusion obtained from the full original polynomial certificate.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
--   - encoding: written monomials and clause occurrences plus unary coefficient mass → collected integer MvPolynomial monomials, positive explicit encoding charges and a list of weighted parity clauses; reason: the source fixes no binary serialization; all written occurrences and unary coefficients are charged, and arbitrary exponents remain allowed
--   - generalization: a certificate of size S → a certificate of charged size at most S; reason: the proof uses only upper bounds by S and the exactly-sized source certificate is included
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.7–8, Lemma 2.4, equation (2.7)

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_certificateSyntax

namespace UnaryParityLifting.Exact

/-- Alekseev, STOC 2027 submission #567 (October 2026), p.7, Lemma 2.4.
Section 2 omits tautological clauses; no squarefree-input hypothesis is imposed. -/
theorem normalization (v S : ℕ) (H : LiftSAParity.CNF (Fin v))
    (hH : SourceCNF H) (enc : EncodingCharge (Fin v))
    (hcert : HasParityCertificate H enc S) :
    ∃ q : NormalizedCertificate H,
      q.Valid ∧ q.axiomMass ≤ S ∧ q.mass ≤ (v + 2) * S ∧ q.axiomSupport ≤ S := by sorry

end UnaryParityLifting.Exact
