-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P06_pureEprMarginal_product
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P06.pureEprMarginal_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:04:59.190316+00:00
-- url     : https://prove2.me/theorems/110c1f2f-1918-48ec-87f6-1593c518749e
-- title:
--   An EPR marginal factors from the third system
-- statement:
--   Let Alice and Bob be qubits, let $E$ be any Hilbert space, and let $\omega_{ABE}$ be a positive trace-class density operator of trace one. Put $P_\Phi=|\Phi\rangle\langle\Phi|$ for $\Phi=(|00\rangle+|11\rangle)/\sqrt{2}$. If $\operatorname{Tr}_E\omega=P_\Phi$, then the computed marginal $\tau_E=\operatorname{Tr}_{AB}\omega$ is a density operator and
--
--   $$
--   \omega_{ABE}=P_\Phi\otimes\tau_E.
--   $$
--
--   There is no dimension bound on $E$, and neither $\omega$ nor $\tau_E$ is required to be pure.
--
--   This is the decoupling fact used in the EPR non-shareability and secrecy arguments. **Formalization Note:** arbitrary orthonormal coordinates represent $E$; nuclearity, positivity and normalization are explicit. The source's ket notation for Joe in equation (2) is read as density-operator shorthand, consistent with the stated purity of the AB marginal alone.
-- source:
--   Is Entanglement Monogamous?, arXiv:quant-ph/0307120v1, PDF p. 5, Section II, explicit supporting result: a pure EPR marginal decouples the third system

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

open QAlgorithms.Papers.Independent.Frontier18.P09 (partialTraceRightCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section II, arXiv:quant-ph/0307120v1, PDF p.5, factorization preceding
(2): an exact EPR marginal forces product with the computed third marginal.
Printed: Joe is written as a ket in (2). Changed: a possibly mixed density.
Why: only the AB marginal is assumed pure; a mixed Joe is allowed by the prose.
The normalization is the 1/sqrt(2) displayed in both (1) and the rendered (2).
This source correction requires independent moderation. -/
theorem pureEprMarginal_product {E : Type}
    (omega : Matrix ((Opinion × Opinion) × E) ((Opinion × Opinion) × E) ℂ)
    (hstate : IsCoordinateDensity omega) (hepr : partialTraceRightCoeff omega = eprDensity) :
    IsCoordinateDensity (traceLeft omega) ∧
      omega = Matrix.kronecker eprDensity (traceLeft omega) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P06

end
