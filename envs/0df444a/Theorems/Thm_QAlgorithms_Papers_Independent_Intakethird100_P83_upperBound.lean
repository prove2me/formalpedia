-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_upperBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.upperBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:07:23.448871+00:00
-- url     : https://prove2.me/theorems/0745500a-fc65-464d-b02f-257678826d0c
-- title:
--   The SDP measure bounds PPT distillable entanglement
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on arbitrary nonzero finite-dimensional complex spaces $A\otimes B$. Partial transpose $T_B$ is taken in a fixed product basis. For $k>0$, let $F_\Gamma(\rho,k)$ be the maximum of $\operatorname{Re}\operatorname{Tr}(\rho Q)$ subject to $0\le Q\le I$ and $-I/k\le T_B(Q)\le I/k$. Define $E_\Gamma(\rho)$ as the supremum of real rates $r$ for which $F_\Gamma(\rho^{\otimes n},2^{nr})\to1$. Define $W(\rho)$ by SDP (7), maximizing $\operatorname{Re}\operatorname{Tr}(T_B(\rho)R)$ over Hermitian $R$ with $\|R\|_\infty\le1$ and $T_B(R)\ge0$, and put $E_W(\rho)=\log_2W(\rho)$. Then every achievable rate $r$ satisfies $r\le E_W(\rho)$, and
--
--   $$E_\Gamma(\rho)\le E_W(\rho).$$
--
--   This gives an upper bound on vanishing-error PPT distillation without assuming that its supremum rate is achieved.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 3, Theorem 1; abstract seed: the new upper bound

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

/-- Theorem 1, PDF p.3: every achievable rate, hence its supremum, is bounded
by E_W. There is no assumption that E_Gamma itself is achievable. -/
theorem upperBound [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ r : ℝ, PPTAchievableRate rho r → r ≤ entanglementW rho) ∧
      entanglementGamma rho ≤ entanglementW rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
