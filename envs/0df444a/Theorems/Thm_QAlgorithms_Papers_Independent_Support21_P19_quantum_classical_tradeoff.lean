-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_quantum_classical_tradeoff
-- name    : QAlgorithms.Papers.Independent.Support21.P19.quantum_classical_tradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:12:42.844921+00:00
-- url     : https://prove2.me/theorems/593d139c-2798-4edb-9649-b32f0db2f522
-- title:
--   Eq. (10): quantum capacity from the classical tradeoff curve
-- statement:
--   Let $U$ be a finite-dimensional bipartite unitary gate and let $e\in\mathbb R$. Define $Q_e(U)$ independently as the extended-real supremum of achievable forward qubit rates with net entanglement budget $e$. Whenever $Q_e(U)$ is a finite real number $q$, one has
--
--   $$
--   q=\frac12 C_{e+q}(U).
--   $$
--
--   The entire expression $e+q$ is the entanglement-budget subscript of the classical capacity. Both capacities use sequential operational protocols and asymptotic simulation with arbitrary rate slack and vanishing error. Infeasible budgets remain $-\infty$ and are not coerced to zero. This is an implicit capacity identity, without a claim of uniqueness for arbitrary solutions of a fixed-point equation.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 4, Eq. (10): quantum capacity from the classical tradeoff curve

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Eq. (10): identity on the feasible finite real-valued qubit-capacity domain.
The entire e+q is the subscript of C. No extended-real value is coerced to zero. -/
theorem quantum_classical_tradeoff (U : Resource) (hU : IsUnitaryResource U) (e q : ℝ)
    (hq : CapacityQ U e=(q : EReal)) :
    (q : EReal)=(1/2 : EReal)*CapacityC U (e+q) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
