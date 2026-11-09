-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_matching_sign_parity
-- name    : PfaffianRecognition.Recognition.matching_sign_parity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T04:39:19.89313+00:00
-- url     : https://prove2.me/theorems/cd0c4fa2-1d30-4f0b-8244-7562709ab0ce
-- title:
--   Lemma 2.1 — matching sign from crossing and reversal parity
-- statement:
--   Let $G$ be a finite simple ordered graph, $D$ an orientation and $M$ any perfect matching. Let $\operatorname{sign}_D(M)$ be the integer sign of the permutation listing oriented tails and heads. Let $\operatorname{cr}(M)$ be the parity of the number of crossing edge pairs and $\operatorname{rev}_D(M)$ the parity of the number of backward matching edges. Then
--   $$
--   \operatorname{sign}_D(M)=(-1)^{\operatorname{cr}(M)+\operatorname{rev}_D(M)}.
--   $$
--   The formula relates a permutation-defined sign to independently counted combinatorial parities. It includes the empty matching on the empty graph, whose sign is $+1$.
--
--   **Formalization Note** The equality is over the integers; signs have not been identified in a characteristic-two field.
--
--   Differences from the source:
--   - encoding: finite simple ordered graphs with labels 1 through N → SimpleGraph (Fin N), with source labels equal to Lean indices plus one; reason: order-preserving relabeling covers every finite simple graph
--   - encoding: any enumeration of oriented edge blocks in the matching permutation → edge blocks sorted by their smaller endpoint, then the sign of the permutation with that one-line sequence; reason: the paper states that changing edge-block order does not change the sign
--   - encoding: parities in F_2 and exponent cr(M)+rev_D(M) → count parities are natural representatives 0 and 1; the exponent is their ordinary sum; reason: powers of minus one depend only on the sum modulo two; the sign remains an integer
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Lemma 2.1, p. 5; definitions in §2.1, pp. 4–5 and §1, p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_graph_model

namespace PfaffianRecognition.Recognition

/-- Lemma 2.1, p. 5. Integer permutation signs, not signs in the characteristic-two field. -/
theorem matching_sign_parity {N : ℕ} (G : SimpleGraph (Fin N)) (D : Orientation G)
    (M : Finset G.edgeSet) (hM : MulmuleyVV.Matching.IsPerfectMatchingEdges G M) :
    matchingSign D M = (-1 : ℤ) ^ (crossingParity M + backwardParity D M) := by sorry

end PfaffianRecognition.Recognition
