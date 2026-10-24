-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P21_scoreOperators
-- name    : QAlgorithms.Papers.Independent.Claimed50.P21.scoreOperators
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:06:44.469353+00:00
-- url     : https://prove2.me/theorems/e2b7db92-0ad3-4a5b-9e3c-6dc4183fa297
-- title:
--   Explicit fidelity and information score operators
-- statement:
--   Let $d\ge2$, use normalized Haar measure on $\mathrm{SU}(d)$, and let $\Xi\succeq0$ commute with $V_3\otimes V_2^*\otimes V_1\otimes V_0^*$ for every special unitary $V$, with $\operatorname{Tr}\Xi=d^2$. Write $P=|I_d\rangle\!\rangle\langle\!\langle I_d|/d$ for the normalized maximally entangled projector. In descending wire order, define
--
--   $$
--   \Lambda_F=\frac{I+d^2P_{32}\otimes P_{10}-P_{32}\otimes I_{10}-I_{32}\otimes P_{10}}{d^2(d^2-1)},\qquad
--   \Lambda_G=\frac{(1-2/d^2)I+I_3\otimes P_{21}\otimes I_0}{d^2(d^2-1)}.
--   $$
--
--   Both operators are positive semidefinite. The covariant density $R_V=A(V,I_d)\Xi A(V,I_d)^\dagger$ is admissible, and its actual physical scores obey
--
--   $$
--   F=\operatorname{Tr}(\Lambda_F\Xi),\qquad G=\operatorname{Tr}(\Lambda_G\Xi),\qquad pG+(1-p)F=\operatorname{Tr}[(p\Lambda_G+(1-p)\Lambda_F)\Xi]\quad(0\le p\le1).
--   $$
--
--   The compatible contraction identity is $\Lambda_G=d^{-1}I_3\otimes(\langle\!\langle I_d|_{30}\Lambda_F|I_d\rangle\!\rangle_{30})\otimes I_0$.
--
--   These formulas connect the physical optimization to a positive matrix objective. **Source correction:** Eq.(27) prints a bare partial trace in place of this Bell-vector contraction. That partial trace gives $I_{21}/d^2$, hence would give $\Lambda_G=I/d^3$, contradicting Eq.(19) and the explicit Eq.(28). Independent moderation of this correction is pending.
-- source:
--   Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation, arXiv:1006.5665v2, PDF p. 6, §IV C, Eqs.(26)–(28), with Eq.(27) correction

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

/-- PDF p.6, Eqs.(26)–(28): explicit positive linear score operators, the
Bell-contraction correction of Eq.(27), and the physical F,G evaluations.
Printed: bare Tr30[lambdaF]. Changed: <<I|30 lambdaF |I>>30. Why: the former
is I21/d^2 and contradicts Eq.(28); the latter follows from Eq.(19).
Independent moderation of this additional source correction remains pending. -/
theorem scoreOperators (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d)
    (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef)
    (hc : SeedCommutes X) (ht : X.trace = (d : ℂ)^2) :
    (lambdaF d).PosSemidef ∧ (lambdaG d).PosSemidef ∧
    lambdaG d = gainBellContraction (lambdaF d) ∧
    IsHaarCombInstrument H (by omega) (covariantDensity X) ∧
    channelScore H (covariantDensity X) = ((lambdaF d * X).trace).re ∧
    gain H (covariantDensity X) = ((lambdaG d * X).trace).re ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      p * gain H (covariantDensity X) + (1-p) * channelScore H (covariantDensity X) =
        ((((p : ℂ) • lambdaG d + ((1-p : ℝ) : ℂ) • lambdaF d) * X).trace).re) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P21

end
