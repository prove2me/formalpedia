-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_localApproximation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_localApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:04:11.903372+00:00
-- url     : https://prove2.me/theorems/a34cac40-79e1-47cf-a870-2b86b8944a99
-- title:
--   Conditional entropy under arbitrary local finite-rank truncations
-- statement:
--   Let rho_AB be a normalized trace-class state on separable complex systems, with H(A)<infinity. Let P_n and Q_k be arbitrary increasing sequences of finite-rank orthogonal projections on A and B, respectively, each converging strongly to identity. For positive mass lambda_nk=Tr[(P_n tensor Q_k)rho_AB(P_n tensor Q_k)], let rho_nk=lambda_nk^{-1}(P_n tensor Q_k)rho_AB(P_n tensor Q_k). At a zero-mass prefix set rho_nk=rho_AB. Then
--   $$\lim_{n,k\to\infty}H(A|B)_{\rho_{nk}}=H(A|B)_\rho.$$
--
--   The limit is along the product order, with both indices independently tending to infinity. Positive mass is eventual, so the zero-prefix convention does not change this approximation result.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 3, §2, proof of Proposition 1, conditional-entropy approximation (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Arbitrary local-projector approximation (10), PDF pp.3–5.
The product atTop filter means n and k tend independently to infinity.
Zero-mass prefixes use the original state; positive mass is eventual. -/
theorem conditionalEntropy_localApproximation {A B : Type} [Countable A] [Countable B]
    (rho : State (A × B)) (hA : homogeneousEntropy (traceSecond rho.coefficients) < ⊤)
    (P : ProjectionApproximation A) (Q : ProjectionApproximation B) :
    Tendsto (fun nk : ℕ × ℕ => finiteFirstConditionalEntropy
      (localCompression rho.coefficients (P.projection nk.1) (Q.projection nk.2)))
      atTop (nhds (finiteFirstConditionalEntropy rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
