-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_exampleC13_properties
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.exampleC13_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:29:14.161647+00:00
-- url     : https://prove2.me/theorems/be94e097-84db-4a93-b59c-b84e9dca14c1
-- title:
--   The explicit three-dimensional algebra-chain example
-- statement:
--   Let $\Phi(X)=\sum_{i=1}^3 K_iXK_i^*$ on $M_3(\mathbb C)$, where
--
--   $$K_1=\frac1{\sqrt2}\begin{pmatrix}0&0&1\\0&0&1\\0&0&0\end{pmatrix},\quad
--   K_2=\frac1{\sqrt2}\begin{pmatrix}1&0&0\\-1&0&0\\0&0&0\end{pmatrix},\quad
--   K_3=\begin{pmatrix}0&0&0\\0&0&0\\0&1&0\end{pmatrix}.$$
--
--   These Kraus operators are normalized; $\Phi$ is CPTP, unital and primitive. Its operator systems are
--
--   $$S_\Phi=\{\operatorname{diag}(a,b,c)\},\quad
--   S_{\Phi^2}=\left\{\begin{pmatrix}a&0&b\\0&c&0\\d&0&e\end{pmatrix}\right\},\quad
--   S_{\Phi^3}=M_3(\mathbb C),$$
--
--   with arbitrary complex entries shown. All three are algebras and both inclusions are strict. Their positive-time scrambling indices satisfy
--
--   $$q(\Phi)=1,\qquad c(\Phi)=c_E(\Phi)=3.$$
--
--   The channel construction is credited to the example after [25, Theorem 3.9]; these capacity calculations are the present paper's application.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 27, Example C.13

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

/-- Example C.13, PDF pp.27–28: the displayed Kraus map, its three computed
systems, strict inclusions, algebra properties and all three scrambling indices.
The construction is credited to [25]; the capacities are this paper's application. -/
theorem exampleC13_properties :
    IsKrausFamily exampleC13Kraus ∧ IsChannel exampleC13 ∧ exampleC13 1 = 1 ∧
    MixingWithFaithfulState exampleC13 ∧
    (graph exampleC13 : Set (Operator 3)) =
      {A | ∀ i j : Fin 3, i ≠ j → A i j = 0} ∧
    (graph (Nat.iterate exampleC13 2) : Set (Operator 3)) =
      {A | A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 2 = 0 ∧ A 2 1 = 0} ∧
    graph (Nat.iterate exampleC13 3) = ⊤ ∧
    graph exampleC13 < graph (Nat.iterate exampleC13 2) ∧
    graph (Nat.iterate exampleC13 2) < graph (Nat.iterate exampleC13 3) ∧
    (∀ n : ℕ, 1 ≤ n → n ≤ 3 → IsOperatorAlgebra (graph (Nat.iterate exampleC13 n))) ∧
    quantumTime exampleC13 = 1 ∧ classicalTime exampleC13 = 3 ∧ assistedTime exampleC13 = 3 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
