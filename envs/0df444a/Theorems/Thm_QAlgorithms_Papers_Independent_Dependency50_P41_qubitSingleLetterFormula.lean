-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_qubitSingleLetterFormula
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.qubitSingleLetterFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:53:58.026974+00:00
-- url     : https://prove2.me/theorems/53eec3bd-a7ba-4f0c-abb2-317261664287
-- title:
--   Two-qubit Choi formula for the single-letter cost
-- statement:
--   Let $\mathcal E$ be a CPTP map with both input and output a single qubit. Let $\phi_2$ be the normalized maximally entangled two-qubit density matrix, $h(t)=-t\log_2t-(1-t)\log_2(1-t)$, and $C$ be two-qubit concurrence: $C(\omega)=\max\{0,\sqrt{\lambda_1}-\sqrt{\lambda_2}-\sqrt{\lambda_3}-\sqrt{\lambda_4}\}$, with decreasing eigenvalues of $\omega\widetilde\omega$ and $\widetilde\omega=(Y\otimes Y)\omega^*(Y\otimes Y)$. Define $E_C^1(\mathcal E)=\max_{\psi\in\mathcal V(AA^\prime)}E_F((\mathcal E\otimes I)(\psi))$. The maximum is attained and $$E_C^1(\mathcal E)=h\!\left(\frac{1+\sqrt{1-C((\mathcal E\otimes I)(\phi_2))^2}}{2}\right).$$
--
--   This computes the single-letter upper-bound quantity, rather than the regularized operational cost.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 15, Unnumbered result, Eq.(77): qubit single-letter formula

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF pp.14–15, (77).
This evaluates ONLY the single-letter quantity E_C^1, not regularized operational E_C. -/
theorem qubitSingleLetterFormula (E : Superop (Fin 2) (Fin 2)) (hE : IsChannel E) :
    IsGreatest (formationOutputs E) (singleLetterCost E) ∧
      singleLetterCost E = binEntropy2 ((1 + Real.sqrt
        (1 - concurrence (idTensorSuperop E (maximallyEntangled 2)) ^ 2)) / 2) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
