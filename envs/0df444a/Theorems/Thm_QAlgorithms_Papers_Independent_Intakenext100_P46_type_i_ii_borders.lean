-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_type_i_ii_borders
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.type_i_ii_borders
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:04:53.443924+00:00
-- url     : https://prove2.me/theorems/6d5dc590-0d72-4785-b12e-94ff662037a5
-- title:
--   §5, Eqs. (37),(38): type (i)/(ii) separability criteria and three-parameter border families
-- statement:
--   Let $\gamma_A,\gamma_B\ge1/2$, $D=\operatorname{diag}(\gamma_A,\gamma_B,\gamma_A,\gamma_B)$ and $x>0$. Construct type-I covariances by $T_IDT_I^T$, where $T_I=(R(-r)\oplus R(r))X(x^{-1})$, and type-II covariances by $T_{II}DT_{II}^T$, where $T_{II}=(\Theta(-\theta)\oplus\Theta(-\theta))X(x^{-1})$. Here $X(x)=\operatorname{diag}(\sqrt{x},x^{-1/2},x^{-1/2},\sqrt{x})$, $R(r)=\begin{pmatrix}\cosh r&\sinh r\\\sinh r&\cosh r\end{pmatrix}$, and $\Theta(t)=\begin{pmatrix}\cos t&\sin t\\-\sin t&\cos t\end{pmatrix}$. For type II require $x>\max\{\sqrt{\gamma_A/\gamma_B},\sqrt{\gamma_B/\gamma_A}\}$ or $0<x<\min\{\sqrt{\gamma_A/\gamma_B},\sqrt{\gamma_B/\gamma_A}\}$. Both constructed covariances are physical. Write $L=(2\gamma_A^2-1/2)(2\gamma_B^2-1/2)$. Separability is equivalent, respectively, to
--   $$L\ge\sinh^2(2r)[(x^2+x^{-2})\gamma_A\gamma_B+\gamma_A^2+\gamma_B^2],$$
--   $$L\ge\sin^2(2\theta)[(x^2+x^{-2})\gamma_A\gamma_B-\gamma_A^2-\gamma_B^2].$$
--   When both eigenvalues exceed $1/2$, equality is equivalent to the actual Gaussian covariance border, and the finite EM is $T^{-T}\operatorname{diag}(m,m)T^{-1}$ with $m_j=\ln((2\gamma_j+1)/(2\gamma_j-1))$. On this border the relevant sine or hyperbolic sine is nonzero. Put $K_I=[L/\sinh^2(2r)-\gamma_A^2-\gamma_B^2]/(\gamma_A\gamma_B)$ or $K_{II}=[L/\sin^2(2\theta)+\gamma_A^2+\gamma_B^2]/(\gamma_A\gamma_B)$. Then $K\ge2$ and
--   $$x=\sqrt{\frac{K+\sqrt{K^2-4}}2}\quad\text{or}\quad x=\sqrt{\frac{K-\sqrt{K^2-4}}2}.$$
--   Thus the finite border search has three independent parameters. The pure-mode separability criteria remain included; scalar equality alone is not used to classify their border. The finite exponential matrix refers to the actual normalized Gibbs density: after a bounded unitary implementing the stated symplectic transformation, its number-basis weights are $\prod_j(1-e^{-m_j})e^{-m_j n_j}$. This operator meaning is part of the conclusion, alongside the covariance normal form.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 8, §5, Eqs. (37),(38): type (i)/(ii) separability criteria and three-parameter border families

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, PDF pp.8–9, (37),(38): separability criteria for constructed
families, finite-chart border equivalences, EM construction, and elimination of
x by the other three parameters. Pure covariances remain in the separability
clauses; they are not declared to be borders from a scalar equality alone. -/
theorem type_i_ii_borders (gA gB : ℝ) (hA : 1 / 2 ≤ gA) (hB : 1 / 2 ≤ gB) :
    (∀ r x : ℝ, 0 < x →
      IsPhysicalCovariance (typeICM gA gB r x) ∧
      (CovSeparable (typeICM gA gB r x) ↔ borderRightI gA gB r x ≤ borderLeft gA gB) ∧
      (1 / 2 < gA → 1 / 2 < gB →
        GaussianEM (typeICM gA gB r x)
          (emFrom (squeezeBoth (-r) * xSqueeze x⁻¹) (pairValues gA gB)) ∧
        (CovBorder (typeICM gA gB r x) ↔ borderRightI gA gB r x = borderLeft gA gB) ∧
        (CovBorder (typeICM gA gB r x) →
          Real.sinh (2 * r) ≠ 0 ∧ PositiveRoots
            ((borderLeft gA gB / Real.sinh (2 * r) ^ 2 - (gA ^ 2 + gB ^ 2)) / (gA * gB)) x))) ∧
    (∀ t x : ℝ, TypeIIDomain gA gB x →
      IsPhysicalCovariance (typeIICM gA gB t x) ∧
      (CovSeparable (typeIICM gA gB t x) ↔ borderRightII gA gB t x ≤ borderLeft gA gB) ∧
      (1 / 2 < gA → 1 / 2 < gB →
        GaussianEM (typeIICM gA gB t x)
          (emFrom (rotateBoth (-t) * xSqueeze x⁻¹) (pairValues gA gB)) ∧
        (CovBorder (typeIICM gA gB t x) ↔ borderRightII gA gB t x = borderLeft gA gB) ∧
        (CovBorder (typeIICM gA gB t x) →
          Real.sin (2 * t) ≠ 0 ∧ PositiveRoots
            ((borderLeft gA gB / Real.sin (2 * t) ^ 2 + (gA ^ 2 + gB ^ 2)) / (gA * gB)) x))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
