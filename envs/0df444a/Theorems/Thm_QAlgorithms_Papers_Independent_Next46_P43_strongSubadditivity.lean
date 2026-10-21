-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_strongSubadditivity
-- name    : QAlgorithms.Papers.Independent.Next46.P43.strongSubadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:44:31.053802+00:00
-- url     : https://prove2.me/theorems/3c3fa57a-961e-4460-9c3d-ba2c438070c4
-- title:
--   Equation (27): strong subadditivity (cited background)
-- statement:
--   Let $\rho_{ABC}$ be a normal state on $B(H_A\otimes H_B\otimes H_C)$ for separable complex Hilbert spaces. Let $\rho_{AB},\rho_{BC},\rho_B$ denote its reduced states. With the von Neumann entropy $S$ taking values in $[0,+\infty]$ and using natural logarithms,
--
--   $$
--   S(\rho_{ABC})+S(\rho_B)\leq S(\rho_{AB})+S(\rho_{BC}).
--   $$
--
--   The inequality allows infinite entropies; the later section assumption of finiteness applies to its equality discussion. This is the strong-subadditivity inequality cited in the paper to Lieb and Ruskai, not a new result claimed by Jenčová and Petz.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 24, Equation (27): strong subadditivity (cited background)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Strong subadditivity (27), PDF p.24, cited there to Lieb–Ruskai [9].
Countable orthonormal coordinates cover all separable complex Hilbert spaces,
including infinite dimensions. The normal state is positive trace class with
trace one. Entropies are extended nonnegative reals in nats; no finiteness
hypothesis from the subsequent equality discussion is imposed on (27). -/
theorem strongSubadditivity
    {I J K : Type} [Countable I] [Countable J] [Countable K]
    (rho : QAlgorithms.Papers.Independent.Dependency50.P33.State (I × (J × K))) :
    QAlgorithms.Papers.Independent.Frontier18.P01.homogeneousEntropy rho.coefficients +
      QAlgorithms.Papers.Independent.Frontier18.P01.homogeneousEntropy
        (QAlgorithms.Papers.Independent.Frontier18.P01.traceSecond
          (QAlgorithms.Papers.Independent.Frontier18.P01.traceFirst rho.coefficients)) ≤
    QAlgorithms.Papers.Independent.Frontier18.P01.homogeneousEntropy
        (MarginalAB rho.coefficients) +
      QAlgorithms.Papers.Independent.Frontier18.P01.homogeneousEntropy
        (QAlgorithms.Papers.Independent.Frontier18.P01.traceFirst rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
