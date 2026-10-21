-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P30_gaussian_chernoffTrace
-- name    : QAlgorithms.Papers.Independent.Claimed50.P30.gaussian_chernoffTrace
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:20:30.213278+00:00
-- url     : https://prove2.me/theorems/de35130f-ded7-489e-bb35-9b317cf6751a
-- title:
--   Gaussian Chernoff trace from physical Williamson data
-- statement:
--   Let $n\ge1$ and let $\rho_A,\rho_B$ be arbitrary Gaussian density operators on the completed $n$-mode oscillator Hilbert space. Use $[\hat x_l,\hat x_m]=2i\Omega_{lm}$ and vacuum covariance $I$. Their physical normal-mode data are $(u_A,S_A,\{\alpha_k\})$ and $(u_B,S_B,\{\beta_k\})$, where every spectral value is at least one and $S_A,S_B$ are symplectic. For $0<s<1$, define
--   $$
--   G_p(x)=\frac{2^p}{(x+1)^p-(x-1)^p},\qquad
--   \Lambda_p(x)=\frac{(x+1)^p+(x-1)^p}{(x+1)^p-(x-1)^p},
--   $$
--   $$
--   V_A(s)=S_A\left[\bigoplus_{k=1}^n\Lambda_s(\alpha_k)I_2\right]S_A^T,\qquad
--   V_B(1-s)=S_B\left[\bigoplus_{k=1}^n\Lambda_{1-s}(\beta_k)I_2\right]S_B^T,
--   $$
--   and write $\Sigma_s=V_A(s)+V_B(1-s)$ and $d=u_A-u_B$. Then $\Sigma_s$ is positive definite and the actual operator product is trace class with
--   $$
--   Q_s:=\operatorname{Tr}(\rho_A^s\rho_B^{1-s})
--   =\frac{2^n\prod_{k=1}^nG_s(\alpha_k)G_{1-s}(\beta_k)}{\sqrt{\det\Sigma_s}}
--   \exp\!\left(-\frac12d^T\Sigma_s^{-1}d\right).
--   $$
--   This is the physical Gaussian power/trace interface needed for Chernoff discrimination. All covariance determinants have dimension $2n$, with every mode's diagonal entry repeated twice; pure modes are allowed.
--
--   **Formalization Note** The left side is defined through bounded-operator continuous functional calculus and the complete number-basis trace, independently of this formula. Trace summability is a conclusion. If $\Pi_s$ is the repeated diagonal with mode entries $G_s(\alpha_k)G_{1-s}(\beta_k)$, its determinant has square root equal to the numerator product. The paper attributes the earlier Gaussian trace formula to Calsamiglia et al. on PDF p.5; this spectral reformulation is stated and proved here.
-- source:
--   Computable bounds for the discrimination of Gaussian states, arXiv:0806.1625v2, PDF p. 4, Theorem 2, Eqs. (52)–(55)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Mathlib supplies this C-star functional calculus as a theorem, not a global instance.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P30

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P04 (Covariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- Theorem 2, arXiv:0806.1625v2, PDF pp.4--5, (52)--(55).
The trace on the left is computed by positive operator powers, not defined by
this determinant identity. Every covariance uses the repeated 2n-dimensional
Williamson diagonal. Formula (52) is stated only for 0<s<1. -/
theorem gaussian_chernoffTrace {n : ℕ} (hn : 0 < n) (W : FockWeylSystem n)
    (A B : GaussianState n W) (DA : NormalModes A) (DB : NormalModes B)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    let Sigma := powerCovariance DA s + powerCovariance DB (1 - s)
    let d := A.mean - B.mean
    IsTraceClass ((positiveOperatorPower A.rho s).comp (positiveOperatorPower B.rho (1 - s))) ∧
    TraceSummable ((positiveOperatorPower A.rho s).comp (positiveOperatorPower B.rho (1 - s))) ∧
    Sigma.PosDef ∧
    trace ((positiveOperatorPower A.rho s).comp (positiveOperatorPower B.rho (1 - s))) =
      (((2 : ℝ) ^ n * (∏ k, spectralG s (DA.spectrum k) *
          spectralG (1 - s) (DB.spectrum k)) / Real.sqrt Sigma.det *
        Real.exp (-quadratic Sigma⁻¹ d / 2) : ℝ) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P30

end
