-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_deterministicSDPs
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.deterministicSDPs
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:15:40.815199+00:00
-- url     : https://prove2.me/theorems/b0be1d64-4d04-4130-8988-d49478677069
-- title:
--   Attained one-copy deterministic SDP characterizations
-- statement:
--   Let $\rho$ be a normalized state on arbitrary nonzero finite-dimensional local spaces, let $P_\rho$ be its orthogonal support projector, and let $F_\Gamma$ be the positive-real-target SDP (3). Independently define $E_1(\rho)=\sup\{\log_2 k:k>0,\ F_\Gamma(\rho,k)=1\}$. Define
--
--   $$\begin{aligned}W_0(\rho)&=\max_R\{\operatorname{Re}\operatorname{Tr}(\rho R):0\le R\le (\operatorname{Re}\operatorname{Tr}(\rho R))I,\ -I\le T_B(R)\le I\},\\m(\rho)&=\min_{P_\rho\le R\le I}\|T_B(R)\|_\infty.\end{aligned}$$
--
--   Both extrema are attained, $W_0(\rho)\ge1$, $m(\rho)>0$, and
--
--   $$E_1(\rho)=\log_2W_0(\rho)=-\log_2m(\rho).$$
--
--   The defining supremum for $E_1$ is also attained at some positive real $k$. This is equivalent to (15), maximizing the negative logarithm over the support interval; the norm minimization itself is the SDP.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 5, Unnumbered main result: one-copy deterministic SDPs (14)–(15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Eqs. (14)–(15), PDF p.5, using the independent F_Gamma definition of
oneCopyExact on p.4. Both SDP optima and the positive-real target size are attained;
the norm is minimized before applying the negative logarithm. -/
theorem deterministicSDPs [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    oneCopyExact rho = Real.logb 2 (wZeroValue rho) ∧
    oneCopyExact rho = -Real.logb 2 (supportNormMinimum rho) ∧
    1 ≤ wZeroValue rho ∧ 0 < supportNormMinimum rho ∧
    (∃ R, WZeroFeasible rho R ∧ effectProb rho R = wZeroValue rho) ∧
    (∃ R, Loewner (supportProjector rho) R ∧ Loewner R 1 ∧
      complexSpectralNorm (partialTranspose R) = supportNormMinimum rho) ∧
    (∃ k : ℝ, 0 < k ∧ pptDistillationFidelity rho k = 1 ∧ oneCopyExact rho = Real.logb 2 k) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
