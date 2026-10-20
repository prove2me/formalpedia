-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_sharpClassicalExample
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.sharpClassicalExample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:22:07.8712+00:00
-- url     : https://prove2.me/theorems/b0f0e364-7749-4d85-b349-0a3a6a05b178
-- title:
--   Explicit sharp classical family, including assisted index
-- statement:
--   The indices $q,c,c_E$ are the first positive iteration times at which the respective capacities $Q_0,C_0,C_{0E}$ vanish; an index is $+\infty$ if no such time exists.
--
--   For $d\ge2$, let $A_d$ be the column-stochastic matrix whose column $0$ is $e_{d-1}$, column $1$ is $(e_0+e_{d-1})/2$, and column $j\ge2$ is $e_{j-1}$. The corresponding CPTP classical channel is $\Phi_{A_d}(X)=\operatorname{diag}(A_d\operatorname{diag}X)$. Then
--
--   $$c(\Phi_{A_d})=c_E(\Phi_{A_d})=\left\lceil\frac{d^2-2d+2}{2}\right\rceil.$$
--
--   This is the explicit family giving the classical quadratic scaling. The stochastic formula is credited to [1], translated to assisted scrambling by B.12.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 21, §B.4, unnumbered sharp classical example

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

/-- Section B.4 sharp family, PDF pp.20–21, using the stochastic formula cited
from [1] and the translation in B.12. The displayed family is defined for d>=2. -/
theorem sharpClassicalExample {d : ℕ} (hd : 2 ≤ d) :
    ColumnStochastic (sharpMatrix d) ∧ IsChannel (Information100.P62.classicalChannel ((sharpMatrix d).map Complex.re)) ∧
    classicalTime (Information100.P62.classicalChannel ((sharpMatrix d).map Complex.re)) = (scramblingBound d : WithTop ℕ) ∧
    assistedTime (Information100.P62.classicalChannel ((sharpMatrix d).map Complex.re)) = (scramblingBound d : WithTop ℕ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
