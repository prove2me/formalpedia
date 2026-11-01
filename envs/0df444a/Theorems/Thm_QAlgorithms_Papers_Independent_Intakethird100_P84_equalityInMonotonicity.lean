-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_equalityInMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.equalityInMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:05:13.768372+00:00
-- url     : https://prove2.me/theorems/b17dfc00-9236-4f96-afd9-3608c02e838e
-- title:
--   Theorem 2: equality in monotonicity (seed paper result)
-- statement:
--   Let $H$ and $K$ be nonzero finite-dimensional complex Hilbert spaces, and let $T:B(H)\to B(K)$ be complex-linear, trace preserving and 2-positive. Let $D_1,D_2$ be invertible density matrices whose images $T(D_1),T(D_2)$ are also invertible. Density matrices are positive semidefinite with ordinary trace one. Write $S(A,B)=\operatorname{Tr}[A(\log A-\log B)]$, using natural logarithms, and let $T^*$ be the computed trace adjoint. Then each of the following is separately equivalent to $S(D_1,D_2)=S(T(D_1),T(D_2))$:
--
--   $$
--   \begin{aligned}
--   &T^*(T(D_1)^{it}T(D_2)^{-it})=D_1^{it}D_2^{-it}\quad\text{for every }t\in\mathbb R,\
--   &T^*(\log T(D_1)-\log T(D_2))=\log D_1-\log D_2.
--   \end{aligned}
--   $$
--
--   This characterizes exactly when coarse graining preserves the relative entropy of a faithful pair. No commutativity, complete positivity or unitality of $T$ is assumed.
--
--   **Formalization Note** The frozen relative entropy includes the correction $-A+B$, whose trace vanishes for trace-one densities. The adjoint is calculated from matrix units; powers are $\exp(it\log A)$.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 5, Theorem 2: equality in monotonicity (seed paper result)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.5, Theorem 2.
Both printed characterizations are individually equivalent to entropy equality.
All four densities are invertible; T is only two-positive and trace preserving. -/
theorem equalityInMonotonicity {I J : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hT : IsTwoPositive T) (htrace : ∀ B, (T B).trace = B.trace)
    (D1 D2 : Matrix I I ℂ)
    (hD1 : IsDensityMatrix D1) (hD2 : IsDensityMatrix D2)
    (hTD1 : IsDensityMatrix (T D1)) (hTD2 : IsDensityMatrix (T D2))
    (hInvD1 : IsUnit D1) (hInvD2 : IsUnit D2)
    (hInvTD1 : IsUnit (T D1)) (hInvTD2 : IsUnit (T D2)) :
    ((qRelEntropy D1 D2 = qRelEntropy (T D1) (T D2)) ↔
      ∀ t : ℝ, traceAdjoint T (imaginaryPower (T D1) t * imaginaryPower (T D2) (-t)) =
        imaginaryPower D1 t * imaginaryPower D2 (-t)) ∧
    ((qRelEntropy D1 D2 = qRelEntropy (T D1) (T D2)) ↔
      traceAdjoint T (cfc Real.log (T D1) - cfc Real.log (T D2)) =
        cfc Real.log D1 - cfc Real.log D2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
