-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_commutingOutputs
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.commutingOutputs
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:06:03.025378+00:00
-- url     : https://prove2.me/theorems/2c4b926a-b3aa-4418-b389-e4dbb82f1c9c
-- title:
--   Corollary 1: commuting outputs force commuting inputs under equality
-- statement:
--   Let $T:B(H)\to B(K)$ be a complex-linear, 2-positive, trace-preserving map between finite-dimensional complex matrix algebras. Suppose $D_1,D_2,T(D_1),T(D_2)$ are invertible density matrices and the two output densities commute. With natural-log relative entropy $S$,
--
--   $$
--   S(D_1,D_2)=S(T(D_1),T(D_2))\quad\Longrightarrow\quad D_1D_2=D_2D_1.
--   $$
--
--   Thus entropy preservation transfers commutativity of the outputs back to the original pair. This is a one-way implication and imposes no commutativity hypothesis on the inputs.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 6, Corollary 1: commuting outputs force commuting inputs under equality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.6, Corollary 1.
Under entropy equality, commuting outputs imply commuting inputs. -/
theorem commutingOutputs {I J : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hT : IsTwoPositive T) (htrace : ∀ B, (T B).trace = B.trace)
    (D1 D2 : Matrix I I ℂ)
    (hD1 : IsDensityMatrix D1) (hD2 : IsDensityMatrix D2)
    (hTD1 : IsDensityMatrix (T D1)) (hTD2 : IsDensityMatrix (T D2))
    (hInvD1 : IsUnit D1) (hInvD2 : IsUnit D2)
    (hInvTD1 : IsUnit (T D1)) (hInvTD2 : IsUnit (T D2))
    (hcomm : Commute (T D1) (T D2))
    (heq : qRelEntropy D1 D2 = qRelEntropy (T D1) (T D2)) :
    Commute D1 D2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
