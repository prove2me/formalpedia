-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_corollaryC28
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.corollaryC28
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:35:17.163967+00:00
-- url     : https://prove2.me/theorems/f9b2c505-3261-4907-b773-fbcaa421d8b0
-- title:
--   Corrected sharp positivity bound for both covariant families
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
--   Suppose $A$ is primitive and both maps are channels. Write $w$ for the first positive strictly-positive power, with infinity when no such power exists. Then
--
--   $$w(\Phi_{A,B})=w(\Phi_{A,C})=w(A)\le d^2-2d+2.$$
--
--   For $d\ge2$, equality holds for the same matrix $A_d$ whose columns are $e_{d-1}$, $(e_0+e_{d-1})/2$, and $e_{j-1}$ for $j\ge2$.
--
--   This is the strict-positivity counterpart of C.27.
--
--   **Formalization Note** The printed ceiling-half bound is replaced by the full quadratic bound fixed by C.25. For $d=2$, $A_d$ has a zero entry and its square is positive, so $w(A_d)=2$ rather than $1$.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 32, Corollary C.28

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

/-- Corollary C.28, PDF p.32, SOURCE CORRECTION: printed ceiling-half bound
is replaced by d^2-2d+2, as uniquely fixed by C.25 (p.31). At d=2 the sharp
matrix is not strictly positive but its square is, so the printed bound 1 fails. -/
theorem corollaryC28 {d : ℕ} (hd : 0 < d) (A B C : Operator d)
    (hA : ColumnStochastic A) (hprim : MatrixPrimitive A)
    (hAB : IsChannel (cduc A B)) (hAC : IsChannel (duc A C)) :
    wielandtTime (cduc A B) = wielandtTime (duc A C) ∧
    wielandtTime (duc A C) = matrixWielandtTime A ∧
    matrixWielandtTime A ≤ (wielandtBound d : WithTop ℕ) ∧
    (2 ≤ d → A = sharpMatrix d →
      wielandtTime (cduc A B) = (wielandtBound d : WithTop ℕ) ∧
      wielandtTime (duc A C) = (wielandtBound d : WithTop ℕ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
