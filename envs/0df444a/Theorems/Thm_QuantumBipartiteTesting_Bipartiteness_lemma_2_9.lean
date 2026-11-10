-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_9
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:12:54.112145+00:00
-- url     : https://prove2.me/theorems/54aabdf9-42d0-49f8-bf4d-6c0fa550f1e0
-- title:
--   Lemma 2.9 — multi-outcome acceptance polynomial
-- statement:
--   Fix arbitrary finite query indices and non-null responses, an injective binary response encoding, and an actual complex quantum circuit making $q$ XOR queries, with arbitrary finite workspace and a fixed output event. Its constructed canonical response-table polynomial $P_A$ is real and multilinear, and
--   $$\deg P_A\le2q,\qquad P_A((\mathbf1_{O(a)=z})_{a,z})=\Pr[A^O\text{ accepts}]$$
--   for every response word $O$. Null responses are eliminated, each indicator occurs at most once, and incompatible answers at one query never occur in a canonical table. This is the arbitrary-response statement needed for graph oracles; it does not re-pose the existing Boolean-phase special case.
--
--   Differences from the source:
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 2.9, PDF = printed page 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_2_9 {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) :
    (CanonicalPolynomial E A out).totalDegree ≤ 2*q ∧
    (∀ az, (CanonicalPolynomial E A out).degreeOf az ≤ 1) ∧
    ∀ O : I → Option S,
      MvPolynomial.eval (Indicators O) (CanonicalPolynomial E A out) = Accept E A out O := by sorry

end QuantumBipartiteTesting.Bipartiteness
