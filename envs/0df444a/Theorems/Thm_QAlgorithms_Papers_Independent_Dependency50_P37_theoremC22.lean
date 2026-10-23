-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremC22
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremC22
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:33:01.10334+00:00
-- url     : https://prove2.me/theorems/880a75a0-9628-4fd7-a2cb-09981f964829
-- title:
--   CDUC and DUC primitive criteria
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
--   Primitivity means mixing with a faithful invariant density for the channel, and mixing with a full-support invariant probability vector for A.
--
--   $$\Phi_{A,B}\text{ is primitive}\iff A\text{ is primitive},\qquad\Phi_{A,C}\text{ is primitive}\iff A\text{ is primitive}.$$
--
--   This transfers the property exactly between each channel family and its classical transition matrix.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 30, Theorem C.22

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

/-- Theorem C.22, PDF pp.30–31: both primitive-channel equivalences. -/
theorem theoremC22 {d : ℕ} (hd : 0 < d) (A : Operator d)
    (hA : ColumnStochastic A) :
    (∀ B : Operator d, IsChannel (cduc A B) → (MixingWithFaithfulState (cduc A B) ↔ MatrixPrimitive A)) ∧
    (∀ C : Operator d, IsChannel (duc A C) → (MixingWithFaithfulState (duc A C) ↔ MatrixPrimitive A)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
