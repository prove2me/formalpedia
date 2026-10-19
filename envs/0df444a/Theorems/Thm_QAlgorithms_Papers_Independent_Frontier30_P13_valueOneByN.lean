-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P13_valueOneByN
-- name    : QAlgorithms.Papers.Independent.Frontier30.P13.valueOneByN
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:19:05.605985+00:00
-- url     : https://prove2.me/theorems/5c990e06-be28-4a13-b4d3-ba90740592e9
-- title:
--   The value for one-by-N Gaussian systems
-- statement:
--   Let $N\ge1$, and let $\gamma$ be a finite physical covariance of one bosonic mode at $A$ and $N$ modes at $B$. Define $V(\gamma)$ using physical local covariance lower bounds, and let $\lambda_{\min}(\gamma)$ denote the smallest symplectic eigenvalue of the covariance after partial transpose on $A$. Then
--
--   $$V(\gamma)=\min\{\lambda_{\min}(\gamma),1\}.$$
--
--   Thus the upper bound in Eq.(A3) is attained throughout the one-by-$N$ setting. The clamp retains the separable regime, in which the eigenvalue may exceed one.
--
--   **Formalization Note** The printed lower bound omits this clamp outside the preceding paragraph's eigenvalue-below-one regime. The correction is recorded explicitly and awaits independent moderation.
-- source:
--   The characterization of Gaussian operations and Distillation of Gaussian States, arXiv:quant-ph/0204085v4, PDF p. 7, Appendix A(4): V and negativity for one-by-N systems

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

/-- Appendix A(4), PDF p.7, with Eq.(A3): for 1-by-N Gaussian systems V equals
the smallest partially transposed symplectic eigenvalue clamped by 1.
Printed: V >= lambdaMin. Changed: min(lambdaMin,1), extending the preceding
paragraph's lambdaMin < 1 regime to separable inputs. Thermal G=2I has
lambdaMin=2 and V=1. Independent moderation of this correction is pending. -/
theorem valueOneByN (n : ℕ) (hn : 0 < n)
    (G : Matrix (BipPhase (Fin 1) (Fin n)) (BipPhase (Fin 1) (Fin n)) ℝ)
    (hG : physicalCovariance G (bipJ (Fin 1) (Fin n))) :
    valueV G = min (lambdaMin G) 1 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P13

end
