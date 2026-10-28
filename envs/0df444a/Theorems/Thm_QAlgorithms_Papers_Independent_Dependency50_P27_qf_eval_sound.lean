-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_qf_eval_sound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.qf_eval_sound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:58:02.293834+00:00
-- url     : https://prove2.me/theorems/87798769-b7ff-40f3-b7c6-59b94eb403f4
-- title:
--   §6.1, soundness of qf_eval
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Terms use natural-number variable names, constants in $R$, addition, negation, multiplication, and total inverse with $0^{-1}=0$. Formulas contain comparisons, Boolean connectives, and named quantifiers. For an environment list $e$ and a quantifier-free formula $f$, Boolean evaluation and propositional interpretation agree:
--
--   $$\operatorname{holds}(e,f)\iff\operatorname{qfEval}(e,f)=\mathrm{true}.$$
--
--   The quantifier-free restriction is an explicit hypothesis; no decision claim is made for formulas still containing quantifiers.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 30, §6.1, soundness of qf_eval

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 30, soundness of qf_eval with the restriction in the binders. -/
theorem qf_eval_sound {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (e : List R) (f : Formula R) (hf : qfForm f = true) :
    holds e f ↔ qfEval e f = true := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
