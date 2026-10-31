-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_indicator_measure_conditions
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.indicator_measure_conditions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:48:01.345339+00:00
-- url     : https://prove2.me/theorems/8e45f269-7322-4b1a-97a3-def85453902b
-- title:
--   Unnumbered: indicator measure satisfies E1–E3
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Define $E_{\mathrm{ind}}(\sigma)=0$ for separable states and $1$ otherwise. This functional vanishes exactly on separable states, is invariant under local unitaries, and for every complete product-Kraus family $V_i=A_i\otimes B_i$, with $p_i=\operatorname{Tr}(V_i\sigma V_i^\dagger)$, obeys
--
--   $$\sum_{i:p_i>0}p_i E_{\mathrm{ind}}\!\left(\frac{V_i\sigma V_i^\dagger}{p_i}\right)\le E_{\mathrm{ind}}(\sigma).$$
--
--   It therefore satisfies all three source conditions E1–E3.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 19, Unnumbered: indicator measure satisfies E1–E3

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

/-- PDF p.19: the indicator measure satisfies all three conditions, including expected E3. -/
theorem indicator_measure_conditions {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] :
    MeasureConditions (entanglementIndicator (I := I) (J := J)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
