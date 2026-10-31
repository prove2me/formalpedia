-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_w_state_yields
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.w_state_yields
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:45:06.258252+00:00
-- url     : https://prove2.me/theorems/3b25e5bc-d5c5-45a1-a480-aebe5f89896e
-- title:
--   Example 11: assisted EPR and GHZ yields from W
-- statement:
--   Let $|W\rangle=(|001\rangle+|010\rangle+|100\rangle)/\sqrt3$, $h=H_2(1/3)$, and $e=H_2((1-\sqrt{5/9})/2)$. Any two parties can distill Bell pairs at rate $h$ with assistance from the third. The $AB$ marginal has single-copy formation $E_F(W^{AB})=e$, and helper $C$ permits the simultaneous rates $(h-e,e)$ for GHZ states and $AB$ Bell pairs. Under unrestricted LOCC,
--
--   $$R_{\rm GHZ}\ge h-\frac e2=H_2(1/3)-\frac12H_2\!\left(\frac{1-\sqrt{5/9}}2\right).$$
--
--   The final rate uses symmetric time sharing to obtain Bell pairs on different edges before converting them to GHZ states. No equality $E_C=E_F$ for this marginal is assumed. These formulas retain exact constants instead of rounded decimal rates.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 7, Example 11: assisted EPR and GHZ yields from W

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF pp.6--7, Example 11: assisted pair yield, coherent GHZ/EPR tradeoff,
and overall GHZ yield after symmetric time sharing across different edges.
Exact entropy expressions are retained. Single-copy W-to-GHZ impossibility
is cited background [1], not a new claimed proof of this paper. -/
theorem w_state_yields :
    let rho := pureDensity symmetricWKet
    let h := binEntropy2 (1/3)
    let e := binEntropy2 ((1 - Real.sqrt (5/9 : ℝ))/2)
    (∀ a b : Fin 3, a ≠ b → AssistedYield rho .locc a b 0 h) ∧
    Information100.P08.formation (pairMarginal rho 0 1) = e ∧
    AssistedYield rho (.broadcast 2) 0 1 (h-e) e ∧
    AssistedYield rho .locc 0 1 (h-e/2) 0 := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
