-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremC21
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremC21
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:32:19.256345+00:00
-- url     : https://prove2.me/theorems/37a66139-46f1-42cd-a978-b263594f2e98
-- title:
--   CDUC and DUC scrambling criteria
-- statement:
--   Let $d\ge1$ and let $A\in M_d(\mathbb C)$ be real nonnegative and column stochastic. For arbitrary matrices $B,C$, define
--
--   $$\begin{aligned}
--   \Phi_{A,B}(X)_{ij}&=\begin{cases}\sum_k A_{ik}X_{kk}&i=j,\\ B_{ij}X_{ij}&i\ne j,\end{cases}\\
--   \Phi_{A,C}(X)_{ij}&=\begin{cases}\sum_k A_{ik}X_{kk}&i=j,\\ C_{ij}X_{ji}&i\ne j.\end{cases}
--   \end{aligned}$$
--
--   Each assertion below applies to its own family whenever the displayed map is CPTP. Thus arbitrary unrelated coefficients are not assumed to define a channel.
--
--   For a channel, scrambling means zero one-shot classical zero-error capacity; for A it means every pair of columns has overlapping support.
--
--   $$\Phi_{A,B}\text{ is scrambling}\iff A\text{ is scrambling},\qquad\Phi_{A,C}\text{ is scrambling}\iff A\text{ is scrambling}.$$
--
--   This transfers the property exactly between each channel family and its classical transition matrix.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 30, Theorem C.21

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

/-- Theorem C.21, PDF p.30: both families; matrix scrambling means column overlap. -/
theorem theoremC21 {d : ℕ} (hd : 0 < d) (A : Operator d)
    (hA : ColumnStochastic A) :
    (∀ B : Operator d, IsChannel (cduc A B) → (classicalCapacity (cduc A B) = 0 ↔ MatrixScrambling A)) ∧
    (∀ C : Operator d, IsChannel (duc A C) → (classicalCapacity (duc A C) = 0 ↔ MatrixScrambling A)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
