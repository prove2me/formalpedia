-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_determinant_superadditivity
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.determinant_superadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:39:37.478384+00:00
-- url     : https://prove2.me/theorems/d0b74a57-17a8-403e-9908-ab8a52e88124
-- title:
--   Example 4: qutrit determinant-state superadditivity
-- statement:
--   Let $|\alpha\rangle=(|012\rangle+|120\rangle+|201\rangle-|210\rangle-|102\rangle-|021\rangle)/\sqrt6$ be the three-qutrit determinant state, and write $\omega=\operatorname{Tr}_C|\alpha\rangle\langle\alpha|$. Then
--
--   $$E_A(\omega)=E_F(\omega)=E_C(\omega)=1,\qquad E_A(\omega\otimes\omega)\ge\frac52.$$
--
--   A normalized witness is $|\varphi\rangle=\bigl((|01\rangle-|10\rangle)^{\otimes2}+(|12\rangle-|21\rangle)^{\otimes2}\bigr)/\sqrt8$, grouped across $A_1A_2:B_1B_2$. Its entropy of entanglement is $5/2$ bits. The doubled marginal is a uniform mixture of its orbit under $U_1^{A_1}\otimes U_2^{A_2}\otimes U_1^{B_1}\otimes U_2^{B_2}$. The statement constructs this orbit witness instead of assuming a favorable ensemble. This exhibits strict superadditivity even for two copies of the same state.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 3, Example 4: qutrit determinant-state superadditivity

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

/-- PDF p.3, Example 4: the one-copy values and strict two-copy bound, including
the constructed uniform orbit witness. No ensemble achieving the bound is
assumed. The marginal spectrum has nine entries, only six of them nonzero. -/
theorem determinant_superadditivity :
    assistance determinantMarginal = 1 ∧
    Information100.P08.formation determinantMarginal = 1 ∧
    Dependency50.P42.entanglementCost Dependency50.P42.paperBures determinantMarginal = 1 ∧
    (5/2 : ℝ) ≤ assistance (bipartiteProduct determinantMarginal determinantMarginal) ∧
    ‖superadditiveWitness‖ = 1 ∧
    vnEntropy (traceRight (pureDensity superadditiveWitness)) = (5/2 : ℝ) ∧
    ∃ k : ℕ, 0 < k ∧ ∃ U V : Fin k → Matrix.unitaryGroup (Fin 3) ℂ,
      bipartiteProduct determinantMarginal determinantMarginal =
        ∑ j, ((k : ℂ)⁻¹) • pureDensity (witnessOrbit (U j) (V j)) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
