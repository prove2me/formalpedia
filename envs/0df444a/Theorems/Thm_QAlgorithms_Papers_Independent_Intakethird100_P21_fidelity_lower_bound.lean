-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_fidelity_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.fidelity_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:57:24.138582+00:00
-- url     : https://prove2.me/theorems/83ad67d1-a44f-4491-8ecd-2816dfba3480
-- title:
--   Fidelity-only lower bounds for arbitrary mixed states
-- statement:
--   Let $d\ge2$ and let $\rho$ be an arbitrary density operator on $\mathbb C^d\otimes\mathbb C^d$. Set $F(\rho)=\langle\Phi_d|\rho|\Phi_d\rangle$, where $\Phi_d=d^{-1/2}\sum_j|j,j\rangle$. For pure cost $t(\psi)=2(1-\operatorname{tr}\rho_A^2)$ or $c(\psi)=\sqrt{t(\psi)}$, define $R_g(F)$ to be the minimum of $\sum_jp_jg(\psi_j)$ over finite normalized pure ensembles satisfying only $\sum_jp_jF(|\psi_j\rangle\langle\psi_j|)=F$. These minima are attained, and
--
--   $$
--   \tau(\rho)\ge R_t(F(\rho)),\qquad C(\rho)\ge R_c(F(\rho)).
--   $$
--
--   The ensembles in this relaxation need not represent $\rho$. Equivalently they may be parametrized by Schmidt probabilities and local unitaries; their component fidelities can range over all of $[0,1]$. If $F(\rho)\ge1/d$, there are also the bounds
--
--   $$
--   \tau(\rho)\ge\operatorname{hull}_{[1/d,1]}q_d(F(\rho)),\qquad
--   C(\rho)\ge\operatorname{hull}_{[1/d,1]}\sqrt{q_d}(F(\rho)),
--   $$
--
--   where $q_d(x)$ is the minimum Schmidt tangle subject to $\sum_k\sqrt{\mu_k}=\sqrt{dx}$ and $\operatorname{hull}$ is the lower convex envelope. This reduces a state-dependent lower bound to its squared overlap.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 6, §3.2, (3.9)–(3.10): fidelity-only lower bounds for arbitrary states

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6--7, (3.9)--(3.10): the arbitrary input is mixed.
The relaxed problem permits every component maximallyEntangledOverlap in [0,1]; only the
further raw-profile scalarConvexRoofAtFidelity bound requires the mean F>=1/d. -/
theorem fidelity_lower_bound (d : ℕ) (hd : 2 ≤ d)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    let F := maximallyEntangledOverlap rho
    IsLeast (relaxedValues d pureTangle F) (relaxedRoof d pureTangle F) ∧
    IsLeast (relaxedValues d pureConcurrence F) (relaxedRoof d pureConcurrence F) ∧
    relaxedRoof d pureTangle F ≤ tangle rho ∧
    relaxedRoof d pureConcurrence F ≤ concurrence rho ∧
    (1 / (d : ℝ) ≤ F →
      scalarConvexRoofAtFidelity d (constrainedSchmidtTangle d) F ≤ tangle rho ∧ scalarConvexRoofAtFidelity d (rawC d) F ≤ concurrence rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
