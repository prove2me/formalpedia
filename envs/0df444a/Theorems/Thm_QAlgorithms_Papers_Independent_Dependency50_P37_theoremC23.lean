-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremC23
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremC23
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:33:58.809013+00:00
-- url     : https://prove2.me/theorems/27605a64-40e6-4272-9489-ce92cefaa0d7
-- title:
--   CDUC and DUC mixing criteria
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
--   Mixing means convergence on every input to the trace-times-invariant-density map, or the sum-times-invariant-probability-vector map in the matrix case.
--
--   $$\Phi_{A,B}\text{ is mixing}\iff A\text{ is mixing},\qquad\Phi_{A,C}\text{ is mixing}\iff A\text{ is mixing}.$$
--
--   This transfers the property exactly between each channel family and its classical transition matrix.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 31, Theorem C.23

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

/-- Theorem C.23, PDF p.31: both mixing-channel equivalences. -/
theorem theoremC23 {d : ℕ} (hd : 0 < d) (A : Operator d)
    (hA : ColumnStochastic A) :
    (∀ B : Operator d, IsChannel (cduc A B) → (Mixing (cduc A B) ↔ MatrixMixing A)) ∧
    (∀ C : Operator d, IsChannel (duc A C) → (Mixing (duc A C) ↔ MatrixMixing A)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
