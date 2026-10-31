-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_completely_positive_composition
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.completely_positive_composition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:09:00.039675+00:00
-- url     : https://prove2.me/theorems/70b15011-625c-42cf-b19b-e44e27197feb
-- title:
--   Composition of completely positive Gaussian maps
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   If $E_1,E_2$ are completely positive Gaussian maps, then
--   $$
--   E_2\circ E_1\text{ is a completely positive Gaussian map}.
--   $$
--   The input maps need not preserve trace, be invertible, or have nonzero prefactor; the zero composite is included. This gives closure for successive Gaussian conditioned operations.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 11, Lemma 7: composition of CP Gaussian maps

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Lemma 7: composition of CP Gaussian maps, including the zero map,
without trace-preservation or inverse hypotheses. -/
theorem completely_positive_composition {n : ℕ} (s : CARSystem n)
    (E1 E2 : Superop (Qubits n) (Qubits n)) (h1 : GaussianMap s E1)
    (h2 : GaussianMap s E2) (hc1 : LinearCompletelyPositive E1) (hc2 : LinearCompletelyPositive E2) :
    GaussianMap s (E2 ∘ E1) ∧ LinearCompletelyPositive (E2 ∘ E1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
