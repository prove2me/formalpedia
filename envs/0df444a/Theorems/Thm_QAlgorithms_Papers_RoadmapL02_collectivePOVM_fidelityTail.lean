-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL02_collectivePOVM_fidelityTail
-- name    : QAlgorithms.Papers.RoadmapL02.collectivePOVM_fidelityTail
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:46:48.561881+00:00
-- url     : https://prove2.me/theorems/24ac7f1b-fcf7-4c9f-b99b-38fa5bc61965
-- title:
--   Collective state tomography: finite-copy fidelity tail bound
-- statement:
--   Let $d,n\ge 1$ be integers. Let $\Lambda_{d,n}$ be the partitions of $n$ with at most $d$ rows, let $\bar\lambda=\operatorname{diag}(\lambda_1/n,\ldots,\lambda_d/n)$, and let $\Pi_\lambda$ be the projector onto the full Schur–Weyl summand $Q_\lambda\otimes P_\lambda$ of $(\mathbb C^d)^{\otimes n}$. Write $s_\lambda$ for the Schur character polynomial, so $\dim Q_\lambda=s_\lambda(1,\ldots,1)$.
--
--   Independently of the unknown state, there exists a lawful continuous collective POVM with outcomes $(\lambda,U)\in\Lambda_{d,n}\times U(d)$, reference measure given by counting measure on $\Lambda_{d,n}$ times normalized Haar measure on $U(d)$, and density
--   $$
--   M(\lambda,U)=\frac{\dim Q_\lambda}{s_\lambda(\bar\lambda)}
--   \Pi_\lambda(U\bar\lambda U^\dagger)^{\otimes n}\Pi_\lambda.
--   $$
--   Its reported density matrix is $\hat\rho(\lambda,U)=U\bar\lambda U^\dagger$.
--
--   For every positive semidefinite matrix $\rho\in\mathbb C^{d\times d}$ with $\operatorname{Tr}\rho=1$, the Born outcome law on the input $\rho^{\otimes n}$ is a probability measure. Writing $r=\operatorname{rank}\rho$, for every $\delta\in[0,1]$ it satisfies
--   $$
--   \Pr_{\rho^{\otimes n}}\!\left[F(\hat\rho,\rho)\le 1-\delta\right]
--   \le (n+1)^{3dr}\exp(-2n\delta),
--   \qquad
--   F(\sigma,\rho)=\operatorname{Tr}\sqrt{\sqrt{\sigma}\rho\sqrt{\sigma}}.
--   $$
--
--   This is the original finite-copy fidelity guarantee for the equation-(10) measurement. The same measurement works for every unknown state and automatically gives the bound corresponding to its actual rank.
-- source:
--   Sample-optimal tomography of quantum states, arXiv:1508.01797v2, §V, equations (10) and (14), PDF p. 6. https://arxiv.org/abs/1508.01797v2 . PDF SHA-256: ecfaf36b39d7503888ce6da5cba33a6d5323bea069ffec0226fcf294ee897c05.

import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
import Definitions.Def_QAlgorithms_Defs_SchurTomography
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL02

/-- Haah, Harrow, Ji, Wu and Yu, *Sample-optimal tomography of quantum states*,
arXiv:1508.01797v2, PDF p.6, Section V, equations (10) and (14).
For positive qudit dimension and copy count, the equation-(10) continuous collective
POVM exists independently of the unknown state. Its reference is counting measure on
partitions times normalized Haar measure on U(d); its output is U lambdaBar U adjoint.
For every normalized positive semidefinite input, the infidelity tail has the printed
finite-copy bound with the input's actual rank. Fidelity is unsquared. The implicit
physical threshold domain is the closed interval [0,1], including its two endpoints. -/
theorem collectivePOVM_fidelityTail (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∃ M : Measurements.DensityPOVM (Fin n → Fin d)
        (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ),
      M.reference = Measure.count.prod (Schur.unitaryHaar d) ∧
      (∀ outcome, M.density outcome =
        Tomography.haahDensity hd hn outcome.1 outcome.2) ∧
      (∀ outcome : Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ,
        IsDensityMatrix (Schur.estimate hd hn outcome.1 outcome.2)) ∧
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho),
        let law := Measurements.bornLaw (Measurements.densityOperatorPOVM M)
          (piKron n rho) (Tomography.tensorDensity rho hrho n)
        IsProbabilityMeasure law ∧
        law = Tomography.haahJointLaw hd hn rho hrho ∧
        ∀ delta : ℝ, 0 ≤ delta → delta ≤ 1 →
          law {outcome | rootFidelity (Schur.estimate hd hn outcome.1 outcome.2) rho ≤
            1 - delta} ≤
            ENNReal.ofReal (((n : ℝ) + 1) ^ (3 * d * rho.rank) *
              Real.exp (-2 * (n : ℝ) * delta)) := by sorry

end QAlgorithms.Papers.RoadmapL02
