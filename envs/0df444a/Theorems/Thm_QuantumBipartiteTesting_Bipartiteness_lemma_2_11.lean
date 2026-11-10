-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_11
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:07.342161+00:00
-- url     : https://prove2.me/theorems/282c2432-bfb3-4e28-acc4-bc84fe76a424
-- title:
--   Lemma 2.11 — rational matching-distribution acceptance
-- statement:
--   There is a positive universal degree constant such that, for every visible vertex count, color count, and query count $q$, every finite real linear combination of formal expected acceptance probabilities of actual $q$-query circuits has a rational representation
--   $$f(M,\ell)=\frac{U(M,\ell)}{V(M,\ell)},\qquad V\mid D_q,\qquad\deg U=O(q\log q).$$
--   The representation holds wherever $\ell$ and $D_q$ are nonzero, and its denominator is nonzero there. Each circuit, encoding, output event, signing law and coefficient is fixed independently of $M,\ell$. Taking a one-term combination includes individual acceptance probabilities. This supplies a common denominator for later formal gap statements.
--
--   Differences from the source:
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
--   - encoding: degree O(q log q) → a positive universal multiple of 1 + q log(q+2); reason: the two rates agree as q tends to infinity; the globally defined expression also retains q=0 and q=1 without artificial hypotheses
--   - reading: formal expectation described both by (A.2)–(A.4) and by arbitrary output on overflow → the algebraic partition functional (A.2)–(A.4), followed by signing probabilities and linear extension; reason: these descriptions disagree at N=M=4,l=2: a one-edge moment is 1/2 algebraically versus 1/8 with empty output on overflow; the feasible law stays conditional and its comparison remains a theorem
--   - reading: Definition 3.6 gives structural matching/response consistency and calls it equivalent to positive sampling probability → consistency is the structural condition, without a parameter-dependent positivity certificate; reason: a three-vertex two-color path is structurally consistent but cannot fit any block when N=M=4,l=2; retaining the structural definition preserves the full algebraic pattern domain
--   - encoding: identities of rational functions → real evaluations with l nonzero and D_q nonzero; grid nonvanishing is concluded eventually in the small-query range; reason: division at a pole is undefined in the source; Lean totalized division is never used to certify an identity there
--   - generalization: expected acceptance under the unsigned matching-block law → finite linear combinations also allow YES and NO signed response laws for every color count; reason: the source explicitly notes on page 12 that the extra signing bit leaves the topology denominator and degree unchanged; unsigned circuits are recovered by ignoring the signing register
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 2.11, PDF = printed page 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_2_11 : ∃ Cdeg : ℝ, 0 < Cdeg ∧
    ∀ N colors q t : ℕ, ∀ A : Fin t → FormalCircuit N colors q, ∀ α : Fin t → ℝ,
      RationalDegreeBound q Cdeg (fun M l => ∑ i, α i * (A i).value M l) := by sorry

end QuantumBipartiteTesting.Bipartiteness
