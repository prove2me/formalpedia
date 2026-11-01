-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_uhlmannMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.uhlmannMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:08:34.206762+00:00
-- url     : https://prove2.me/theorems/64f09859-dc2e-4c78-bc50-26e58cc44f20
-- title:
--   Theorem 1 ([23,14]): Uhlmann monotonicity, cited background
-- statement:
--   Let $T:M_I(\mathbb C)\to M_J(\mathbb C)$ be complex linear, 2-positive and trace preserving on nonzero finite spaces. For every pair of density matrices $D_1,D_2$, including singular ones,
--
--   $$S(T(D_1),T(D_2))\le S(D_1,D_2).$$
--
--   Here $S(A,B)=\operatorname{Tr}(A\log A-A\log B)$ when $\operatorname{supp}A\subseteq\operatorname{supp}B$, and $+\infty$ otherwise. No input or output invertibility is assumed.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 2, Theorem 1 ([23,14]): Uhlmann monotonicity, cited background

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.2, Theorem 1 [23,14].
Full-domain extended Umegaki entropy; singular densities and support failure are allowed.
Two-positivity and trace preservation are the only map assumptions. -/
theorem uhlmannMonotonicity {I J : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hT : IsTwoPositive T) (htrace : ∀ B, (T B).trace = B.trace)
    (D1 D2 : Matrix I I ℂ)
    (hD1 : IsDensityMatrix D1) (hD2 : IsDensityMatrix D2) :
    QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy (T D1) (T D2) ≤
      QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy D1 D2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
