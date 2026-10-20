-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_exampleC8_properties
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.exampleC8_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:25:19.827678+00:00
-- url     : https://prove2.me/theorems/43b8c0c7-52d3-43df-a0a0-61ed7ebd9231
-- title:
--   A concrete fully irreducible channel that is not scrambling
-- statement:
--   Define $\Phi:M_4(\mathbb C)\to M_4(\mathbb C)$ by
--
--   $$\Phi(X)=\tfrac12\operatorname{diag}(X_{11}+X_{22},\ X_{22}+X_{33},\ X_{33}+X_{44},\ X_{44}+X_{11}).$$
--
--   This map is CPTP, unital and fully irreducible, but is not scrambling. Writing $E_{ij}$ for matrix units,
--
--   $$\Phi(E_{11})=\tfrac12(E_{11}+E_{44}),\qquad
--   \Phi(E_{33})=\tfrac12(E_{22}+E_{33}),\qquad
--   \operatorname{Tr}(\Phi(E_{11})\Phi(E_{33}))=0.$$
--
--   The two disjoint output supports exhibit a perfectly transmitted bit, disproving the converse of C.7.
--
--   **Formalization Note** Matrix indices start at zero in Lean.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 25, Example C.8

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Example C.8, PDF p.25: concrete map, full irreducibility, and the two
disjoint output supports witnessing failure of the converse to C.7. -/
theorem exampleC8_properties :
    IsChannel exampleC8 ∧ exampleC8 1 = 1 ∧ FullyIrreducible exampleC8 ∧
    classicalCapacity exampleC8 ≠ 0 ∧
    exampleC8 (Matrix.single 0 0 1) =
      (1 / 2 : ℂ) • (Matrix.single 0 0 1 + Matrix.single 3 3 1) ∧
    exampleC8 (Matrix.single 2 2 1) =
      (1 / 2 : ℂ) • (Matrix.single 1 1 1 + Matrix.single 2 2 1) ∧
    OrthogonalOutputs (exampleC8 (Matrix.single 0 0 1))
      (exampleC8 (Matrix.single 2 2 1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
