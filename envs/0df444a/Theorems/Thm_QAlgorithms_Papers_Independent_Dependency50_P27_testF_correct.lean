-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_testF_correct
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.testF_correct
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:59:43.624087+00:00
-- url     : https://prove2.me/theorems/a43becf9-fc07-4bd1-a5e0-c7c0f28bda1a
-- title:
--   §6.2.3, direct leading-coefficient sign test
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For a formal coefficient list $p$, define $\operatorname{testF}(p)=\operatorname{lcoefCps}(p,\ t\mapsto(0<t))$. The output is quantifier-free. For every environment $e$,
--
--   $$\operatorname{qfEval}(e,\operatorname{testF}(p))=[0<\operatorname{lc}(\operatorname{evalPoly}(e,p))].$$
--
--   Here brackets denote the decidable Boolean comparison. The test handles degree drops and the all-zero list without a generic definability assumption.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 34, §6.2.3, direct leading-coefficient sign test

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 34, the concrete quantifier-free leading-coefficient positivity
test, including all-zero and degree-dropping specializations. -/
theorem testF_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : PolyF R) (e : List R) :
    qfForm (testF p) = true ∧
    qfEval e (testF p) = decide (0 < (evalPoly e p).leadingCoeff) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
