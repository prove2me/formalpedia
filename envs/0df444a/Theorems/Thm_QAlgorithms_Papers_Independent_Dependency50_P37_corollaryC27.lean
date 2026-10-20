-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_corollaryC27
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.corollaryC27
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:34:32.7119+00:00
-- url     : https://prove2.me/theorems/c9f1af6c-8317-4fac-81f2-1c08b19895d5
-- title:
--   Corrected sharp scrambling bound for both covariant families
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
--   The indices $q,c,c_E$ are the first positive iteration times at which the respective capacities $Q_0,C_0,C_{0E}$ vanish; an index is $+\infty$ if no such time exists.
--
--   If $A$ is mixing and both maps are channels, then
--
--   $$c(\Phi_{A,B})=c(\Phi_{A,C})=c(A)\le\left\lceil\frac{d^2-2d+2}{2}\right\rceil,$$
--
--   where $c(A)$ is its first positive scrambling power. For $d\ge2$, equality holds when $A=A_d$: its columns are $e_{d-1}$, $(e_0+e_{d-1})/2$, and $e_{j-1}$ for $j\ge2$.
--
--   This gives the sharp classical scaling for both channel families.
--
--   **Formalization Note** The print uses the full quadratic bound and claims sharpness for $A_d$. C.26 and the p.21 example fix the ceiling-half value; C.27/C.28 have exchanged their two bounds.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 32, Corollary C.27

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

/-- Corollary C.27, PDF p.32, SOURCE CORRECTION: printed d^2-2d+2 is replaced
by its ceiling-half value. C.26 (p.31) and B.4's example (p.21) uniquely pin this
scrambling bound; C.27/C.28 exchanged bounds. Equality is retained for A_d, d>=2. -/
theorem corollaryC27 {d : ℕ} (hd : 0 < d) (A B C : Operator d)
    (hA : ColumnStochastic A) (hmix : MatrixMixing A)
    (hAB : IsChannel (cduc A B)) (hAC : IsChannel (duc A C)) :
    classicalTime (cduc A B) = classicalTime (duc A C) ∧
    classicalTime (duc A C) = matrixClassicalTime A ∧
    matrixClassicalTime A ≤ (scramblingBound d : WithTop ℕ) ∧
    (2 ≤ d → A = sharpMatrix d →
      classicalTime (cduc A B) = (scramblingBound d : WithTop ℕ) ∧
      classicalTime (duc A C) = (scramblingBound d : WithTop ℕ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
