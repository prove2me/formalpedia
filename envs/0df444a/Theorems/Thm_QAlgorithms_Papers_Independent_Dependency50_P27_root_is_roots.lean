-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_root_is_roots
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.root_is_roots
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:48:33.848895+00:00
-- url     : https://prove2.me/theorems/bf510cec-aa65-4d4d-a53f-29567fd5e387
-- title:
--   §4.2, Lemma root_is_roots
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $P\ne0$ and $a<x<b$, root membership is characterized by
--
--   $$P(x)=0\iff x\in\operatorname{roots}(P,a,b).$$
--
--   Both the nonzero-polynomial hypothesis and the open-interval restriction are retained.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 19, §4.2, Lemma root_is_roots

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 19, root_is_roots, retaining both guards. -/
theorem root_is_roots {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) (hp : p ≠ 0)
    (x : R) (hx : a < x ∧ x < b) :
    p.eval x = 0 ↔ x ∈ roots p a b := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
