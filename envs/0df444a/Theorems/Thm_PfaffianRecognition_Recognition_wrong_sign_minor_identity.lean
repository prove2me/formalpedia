-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_wrong_sign_minor_identity
-- name    : PfaffianRecognition.Recognition.wrong_sign_minor_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T04:41:47.356669+00:00
-- url     : https://prove2.me/theorems/13ae8b00-0b30-4847-9f1f-7f86558bf3f8
-- title:
--   Lemma 2.3 — wrong-sign polynomial principal-minor identity
-- statement:
--   Let $G$ be a finite simple ordered graph, $D$ an orientation, $F$ a perfect matching of $G$, and $K$ any field of characteristic two. Use $P_{D,F}$ for the formal sum of squared edge monomials over matchings with integer sign opposite to $F$. Let $s=\operatorname{cr}(F)+\operatorname{rev}_D(F)\in\mathbb F_2$, let $R_D$ be the backward edges, let $C(G)$ be the unordered crossing pairs, and let $A_D$ be the weighted skew-adjacency matrix. Then, as formal polynomials over $K$,
--   $$
--   P_{D,F}=s\det A_D+\sum_{e\in R_D}x_e^2\det(A_D-e)
--    +\sum_{\{e,f\}\in C(G)}x_e^2x_f^2\det(A_D-e-f).
--   $$
--   Deleting an edge means deleting its two endpoint rows and columns. This identity supplies the determinant expression used for evaluating the wrong-sign polynomial; it applies to singular matrices as well.
--
--   **Formalization Note** The field can be finite or infinite, exactly as the lemma states. The scalar $s$ is cast from its representative 0 or 1. At an empty principal submatrix the determinant is 1. No finite-field sampling or invertibility assumption is present.
--
--   Differences from the source:
--   - encoding: finite simple ordered graphs with labels 1 through N → SimpleGraph (Fin N), with source labels equal to Lean indices plus one; reason: order-preserving relabeling covers every finite simple graph
--   - encoding: the fixed perfect matching F is suppressed in P_D → F is an explicit parameter with a perfect-matching hypothesis; reason: this is the standing assumption of section 2.2, not an added proof assumption
--   - encoding: unordered crossing pairs and endpoint-deleted matrices → each crossing pair is represented once with increasing left endpoints, and principal submatrices use the complement of the deleted endpoint set; reason: no pair is doubled and no matrix entry is substituted for vertex deletion
--   - encoding: s is the element cr(F)+rev_D(F) of F_2 → s is the natural representative modulo two cast into the coefficient field; reason: 0 and 1 embed as the same prime-subfield elements
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Lemma 2.3, equation (1), p. 6; standing assumptions in §2.2, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_polynomial_model

namespace PfaffianRecognition.Recognition

/-- Lemma 2.3 / equation (1), p. 6, under §2.2's fixed-perfect-matching assumption (p. 5).
Every characteristic-two field is allowed, and singular matrices are included. -/
theorem wrong_sign_minor_identity {N : ℕ} (G : SimpleGraph (Fin N))
    (D : Orientation G) (F : Finset G.edgeSet)
    (hF : MulmuleyVV.Matching.IsPerfectMatchingEdges G F)
    (K : Type*) [Field K] [CharP K 2] :
    wrongSignPolynomial K D F = minorExpression K D F := by sorry

end PfaffianRecognition.Recognition
