-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_wrong_sign_zero_iff
-- name    : PfaffianRecognition.Recognition.wrong_sign_zero_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T04:41:53.095928+00:00
-- url     : https://prove2.me/theorems/1e205351-5e90-4abe-9278-398ded08c4c9
-- title:
--   Proposition 2.2 — formal zero polynomial iff Pfaffian orientation
-- statement:
--   Let $G$ be a finite simple ordered graph, $D$ an orientation, $F$ a fixed perfect matching and $K$ a finite field of characteristic two. Define $P_{D,F}$ by the source's squared-monomial sum over matchings whose integer signs differ from that of $F$. Then
--   $$
--   D\text{ is Pfaffian}\iff P_{D,F}=0.
--   $$
--   Both directions are asserted. The equality is coefficientwise equality of formal polynomials, rather than the claim that every field evaluation vanishes. This is the algebraic characterization used by the orientation test.
--
--   **Formalization Note** The finite-field domain is retained from the preamble of §2.2. The reference matching must be perfect; an arbitrary edge set cannot be used to force the wrong-sign polynomial to be empty. No perfect-matching promise is imposed on the separate graph-recognition goal.
--
--   Differences from the source:
--   - encoding: finite simple ordered graphs with labels 1 through N → SimpleGraph (Fin N), with source labels equal to Lean indices plus one; reason: order-preserving relabeling covers every finite simple graph
--   - encoding: the fixed perfect matching F is suppressed in P_D → F is an explicit parameter with a perfect-matching hypothesis; reason: this is the standing assumption of section 2.2, not an added proof assumption
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Proposition 2.2 and §2.2 standing assumptions, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_polynomial_model

namespace PfaffianRecognition.Recognition

/-- Proposition 2.2, p. 5, with §2.2's fixed reference perfect matching and finite
characteristic-two coefficient field. Zero means equality of formal polynomials. -/
theorem wrong_sign_zero_iff {N : ℕ} (G : SimpleGraph (Fin N)) (D : Orientation G)
    (F : Finset G.edgeSet) (hF : MulmuleyVV.Matching.IsPerfectMatchingEdges G F)
    (K : Type*) [Field K] [Fintype K] [CharP K 2] :
    IsPfaffianOrientation D ↔ wrongSignPolynomial K D F = 0 := by sorry

end PfaffianRecognition.Recognition
