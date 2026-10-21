-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_3_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_3_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:44:08.954591+00:00
-- url     : https://prove2.me/theorems/922b5c82-a80a-403d-a8bf-152810ed9bbb
-- title:
--   Proposition 3.1
-- statement:
--   Let $\nu,\omega$ be faithful positive functionals on a nonzero finite-dimensional complex Hilbert space, represented by positive-definite matrices, with no trace-one requirement. A projection test $T$ accepts $\omega$ at outcome one. Define $D(\nu,\omega,T)=\nu(T)+\omega(1-T)$ and $D(\nu,\omega)=\inf_TD(\nu,\omega,T)$. Let $T_*=s_{(\omega-\nu)_+}$ be the strict positive spectral support. Then
--
--   $$D(\nu,\omega)=D(\nu,\omega,T_*)=\frac{\operatorname{Tr}\omega+\operatorname{Tr}\nu-\operatorname{Tr}|\omega-\nu|}{2}.$$
--
--   The specified optimizing test, including its zero-eigenvalue convention, is retained.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 12, Proposition 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3.1 including the specified optimizing test,
arXiv:1109.3804v2, PDF p.12. -/
theorem proposition_3_1 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (nu omega : Matrix I I ℂ) (hnu : nu.PosDef) (homega : omega.PosDef) :
    optimalError false nu omega = (testingError nu omega (positiveSupport (omega - nu)) : EReal) ∧
    (testingError nu omega (positiveSupport (omega - nu)) : EReal) =
      (((omega.trace.re + nu.trace.re - QAlgorithms.traceNorm (omega - nu)) / 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
