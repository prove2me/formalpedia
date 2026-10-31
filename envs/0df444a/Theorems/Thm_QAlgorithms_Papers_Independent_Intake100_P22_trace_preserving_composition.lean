-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_trace_preserving_composition
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.trace_preserving_composition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:08:12.154876+00:00
-- url     : https://prove2.me/theorems/9768671a-d1a9-4d5d-b84d-78427b5c2a54
-- title:
--   Composition of trace-preserving Gaussian maps
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   If $E_1,E_2$ are trace-preserving Gaussian maps on the full operator algebra, then
--   $$
--   E_2\circ E_1\text{ is a trace-preserving Gaussian map}.
--   $$
--   Complete positivity is not an additional hypothesis. The printed second input $E$ is read as $E_2$, consistently with the conclusion and proof. This supplies closure for successive normalized Gaussian evolutions.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 11, Lemma 6: composition of TP Gaussian maps

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Lemma 6: composition of TP Gaussian maps, with no CP assumption.
The printed second input "E" is corrected to E2, as used in the conclusion
and proof. -/
theorem trace_preserving_composition {n : ℕ} (s : CARSystem n)
    (E1 E2 : Superop (Qubits n) (Qubits n)) (h1 : GaussianMap s E1)
    (h2 : GaussianMap s E2) (ht1 : FullTracePreserving E1) (ht2 : FullTracePreserving E2) :
    GaussianMap s (E2 ∘ E1) ∧ FullTracePreserving (E2 ∘ E1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
