-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_stieltjes_basic
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.stieltjes_basic
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:29:27.169135+00:00
-- url     : https://prove2.me/theorems/49f31cda-d6b9-4feb-9df0-b316d22cca2a
-- title:
--   Stieltjes densities: nonzero L2, radial asymptotics, and polynomials
-- statement:
--   Let $d\geq1$ and let $\rho\neq0$ be a positive Borel measure on $[0,\infty)$. Define the extended nonnegative density $\Theta(x)=\int_0^\infty(y^2+\|x\|^2)^{-1}\,d\rho(y)$ and $\nu=\Theta\,dx$ on $\mathbb R^d$. The following are equivalent: $\Theta(x)<\infty$ for some nonzero $x$; it is finite at every nonzero $x$; $L^2(\nu)\neq\{0\}$; and $\int_0^\infty(1+y^2)^{-1}\,d\rho(y)<\infty$.
--   Under these conditions, $\rho$ is tempered and
--   $$\lim_{\|x\|\to\infty}\Theta(x)\|x\|^2=\rho([0,\infty))>0.$$
--   The limit is allowed to be infinite. There is a nonzero polynomial in $L^2(\nu)$ exactly when $d=1$ and $\nu$ is finite; every polynomial in $L^2(\nu)$ is constant. In dimension one,
--   $$\nu(\mathbb R)=\pi\int_0^\infty y^{-1}\,d\rho(y).$$
--   All reciprocals and integrals here are extended nonnegative quantities, so the reciprocal at zero is infinite.
--
--   This result identifies the nontrivial and polynomial parts of the Stieltjes-measure Hilbert model.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 42, Lemma A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma A.1, PDF pp. 42--43, all equivalences and both additional clauses.
The radial limit and reciprocal at y=0 are extended nonnegative values.
The final total-mass identity is asserted only in dimension one. -/
theorem stieltjes_basic (d : ℕ) (hd : 0 < d) (rho : Measure ℝ≥0) (hRho : rho ≠ 0) :
    ((∃ x : EuclideanSpace ℝ (Fin d), x ≠ 0 ∧ stieltjesDensity d rho x < ⊤) ↔
      ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → stieltjesDensity d rho x < ⊤) ∧
    ((∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → stieltjesDensity d rho x < ⊤) ↔
      Nontrivial (Lp ℂ 2 (stieltjesMeasure d rho))) ∧
    (Nontrivial (Lp ℂ 2 (stieltjesMeasure d rho)) ↔ IsTame rho) ∧
    (IsTame rho →
      IsTemperedMeasure (Measure.map (fun y : ℝ≥0 => (y : ℝ)) rho) ∧
      0 < rho Set.univ ∧
      Filter.Tendsto
        (fun x : EuclideanSpace ℝ (Fin d) =>
          stieltjesDensity d rho x * ENNReal.ofReal (‖x‖ ^ 2))
        (Filter.comap (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) Filter.atTop)
        (nhds (rho Set.univ)) ∧
      ((∃ p : MvPolynomial (Fin d) ℂ, p ≠ 0 ∧
          MemLp (polynomialValue p) 2 (stieltjesMeasure d rho)) ↔
        d = 1 ∧ stieltjesMeasure d rho Set.univ < ⊤) ∧
      (∀ p : MvPolynomial (Fin d) ℂ,
        MemLp (polynomialValue p) 2 (stieltjesMeasure d rho) →
          ∃ c : ℂ, p = MvPolynomial.C c) ∧
      (d = 1 → stieltjesMeasure d rho Set.univ =
        ENNReal.ofReal Real.pi * (∫⁻ y, (y : ℝ≥0∞)⁻¹ ∂rho))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
