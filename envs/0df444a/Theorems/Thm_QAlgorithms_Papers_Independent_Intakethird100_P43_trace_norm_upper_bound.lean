-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P43_trace_norm_upper_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P43.trace_norm_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:21:37.178714+00:00
-- url     : https://prove2.me/theorems/fb76bc47-a0aa-41ea-946d-65c900748ccf
-- title:
--   General trace-norm upper bound for PPT distillation fidelity
-- statement:
--   All operators act on a finite bipartite space $\mathbb C^d\otimes\mathbb C^d$ in a fixed product basis. Write $\Gamma=T_2$ for Bob's partial transpose and $P_m=|\psi_m\rangle\langle\psi_m|$, where $|\psi_m\rangle=m^{-1/2}\sum_i|ii\rangle$. A density operator is positive semidefinite with complex trace exactly one. An admissible PPT map is complex-linear, positive and trace preserving, and $\Gamma_{\rm out}T\Gamma_{\rm in}$ is positive on every positive operator. A PPT channel is additionally completely positive; complete positivity of the transpose-conjugated map is not required. Fidelity means the overlap $\operatorname{tr}(P_m T(\rho))$.
--
--   Let $d,m\ge1$, let $\rho$ be a density operator, and let $A$ be Hermitian with $0\le A\le I$ and $-I\le mA^\Gamma\le I$. Then
--
--   $$\operatorname{tr}(\rho A)=\operatorname{tr}(A^\Gamma\rho^\Gamma)\le\frac{\|\rho^\Gamma\|_1}{m}.$$
--
--   Furthermore every admissible positive PPT map $T$ to local output dimension $m$ satisfies $\operatorname{tr}(P_mT(\rho))\le\|\rho^\Gamma\|_1/m$. This bounds the optimal distillation overlap, including the rank-one target $m=1$; the positive and negative parts in the source's derivation are not independent inputs.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, PDF p. 3, Eq. (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.3, (10): the general trace-norm upper bound, including m=1.
SOURCE CORRECTION: the explanation prints m||A||_1<=1. The actual constraint (2)
is -I<=m Gamma(A)<=I, equivalently ||m Gamma(A)||_infty<=1. We retain (2),
not the misprinted trace-norm constraint. Independent moderation is required. -/
theorem trace_norm_upper_bound (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (rho A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (hA : RainsFeasibleEffect m A) :
    (rho * A).trace.re = (gamma A * gamma rho).trace.re ∧
      (rho * A).trace.re ≤ traceNorm (gamma rho) / (m : ℝ) ∧
      ∀ T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
          Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ,
        IsPPTMap T → effectProb (bellProjector m) (T rho) ≤ traceNorm (gamma rho) / (m : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P43

end
