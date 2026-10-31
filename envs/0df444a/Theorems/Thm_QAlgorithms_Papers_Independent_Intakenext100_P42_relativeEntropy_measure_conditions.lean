-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_relativeEntropy_measure_conditions
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.relativeEntropy_measure_conditions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:42:19.966486+00:00
-- url     : https://prove2.me/theorems/df83e248-7efb-4d1c-bf6c-6bc74cd44a0a
-- title:
--   Unnumbered: relative entropy yields E1–E3
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   The functional $E_R$ vanishes exactly on separable states, is invariant under local unitary conjugation, and satisfies expected monotonicity for every complete product-Kraus family $V_i=A_i\otimes B_i$. With $p_i=\operatorname{Tr}(V_i\sigma V_i^\dagger)$,
--
--   $$\sum_{i:p_i>0}p_i E_R\!\left(\frac{V_i\sigma V_i^\dagger}{p_i}\right)\le E_R(\sigma).$$
--
--   These are E1–E3 in the source’s explicit Eq.(1) operational idealization.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 11, Unnumbered: relative entropy yields E1–E3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.11–12: relative entropy's concrete measure satisfies E1,E2,E3.
This does not assert the defective printed all-projector F1–F5 package. -/
theorem relativeEntropy_measure_conditions {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] :
    MeasureConditions (relativeEntanglementNats (I := I) (J := J)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
