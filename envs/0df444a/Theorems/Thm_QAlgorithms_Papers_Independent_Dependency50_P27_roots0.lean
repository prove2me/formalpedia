-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_roots0
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.roots0
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:47:17.438077+00:00
-- url     : https://prove2.me/theorems/1b6c4a89-d347-4cd5-95e1-49399861f063
-- title:
--   §4.2, Lemma roots0
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Write $\operatorname{roots}(P,a,b)$ for the local derivative/IVT root-isolation procedure on the open interval $(a,b)$. For all endpoints,
--
--   $$\operatorname{roots}(0,a,b)=[].$$
--
--   This fixes the total convention at the zero polynomial.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 19, §4.2, Lemma roots0

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 19, roots0. -/
theorem roots0 {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) : roots (0 : Polynomial R) a b = [] := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
