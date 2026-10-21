-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_3_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_3_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:45:10.533977+00:00
-- url     : https://prove2.me/theorems/d983b173-19be-4e9d-8a52-677a80c2b196
-- title:
--   Proposition 3.3
-- statement:
--   Let $(\nu_n,\omega_n)$ be faithful positive functionals on possibly varying nonzero finite-dimensional complex systems. Let $w_n>0$ tend to infinity, let $D_n$ be the optimal projection-testing sum of errors, and write $\operatorname{Ent}_s(\nu|\omega)=\log\operatorname{Tr}(\nu^s\omega^{1-s})$ with natural logarithms. Then
--
--   $$\limsup_{n\to\infty}w_n^{-1}\log D_n\le\inf_{0\le s\le1}\limsup_{n\to\infty}w_n^{-1}\operatorname{Ent}_s(\nu_n|\omega_n).$$
--
--   The infimum is outside the limsup. Normalization and existence of a Renyi limit are not required.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 13, Proposition 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3.3, arXiv:1109.3804v2, PDF p.13.
The infimum is outside limsup; AF1 and normalization are not assumptions. -/
theorem proposition_3_3 (F : FiniteTestingFamily) :
    Filter.limsup (symmetricRate F false) atTop ≤
      sInf {v | ∃ s ∈ Set.Icc (0 : ℝ) 1, v = Filter.limsup (scaledRenyi F s) atTop} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
