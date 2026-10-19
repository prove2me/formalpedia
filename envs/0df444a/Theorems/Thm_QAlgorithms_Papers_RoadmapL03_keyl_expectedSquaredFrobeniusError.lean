-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_expectedSquaredFrobeniusError
-- name    : QAlgorithms.Papers.RoadmapL03.keyl_expectedSquaredFrobeniusError
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:47:02.20747+00:00
-- url     : https://prove2.me/theorems/e933b3f4-c534-4a22-8b57-e3b0f0bf665d
-- title:
--   Keyl tomography: expected squared Frobenius error at most (4d−3)/n
-- statement:
--   Let $d,n\ge 1$ be integers and let $\rho$ be an arbitrary complex $d\times d$ density matrix, including a singular one. Write $\alpha$ for its decreasingly sorted spectrum. On $n$ independent copies $\rho^{\otimes n}$, perform weak Schur sampling and then Keyl's normalized highest-weight POVM in the Schur module of the observed partition. The first outcome $\lambda$ is a partition of $n$ with at most $d$ rows and has distribution $\mathrm{SW}^n(\alpha)$. Conditional on any positive-probability partition, the second outcome $U\in U(d)$ has law $\mathrm{K}_\lambda(\rho)$. Put $\underline{\lambda}=(\lambda_1/n,\ldots,\lambda_d/n)$, padding the rows by zeros, and report $\widehat\rho=U\operatorname{diag}(\underline{\lambda})U^\dagger$. Then
--
--   $$
--   \mathbb E_{\lambda\sim\mathrm{SW}^n(\alpha),\ U\sim\mathrm K_\lambda(\rho)}\!\left[\|\widehat\rho-\rho\|_F^2\right]\le\frac{4d-3}{n},
--   $$
--
--   where $\|A\|_F^2=\sum_{i,j}|A_{ij}|^2$. The measurement is fixed by $d,n$ before the unknown input state is supplied. This is the paper's expected-risk guarantee for the named estimator.
--
--   **Formalization Note** The theorem also certifies a lawful continuous-outcome POVM, chosen before $\rho$, whose Born law is the frozen computed joint law. The nonnegative risk is a Lebesgue integral in $[0,\infty]$; the finite bound ensures finiteness. The joint density relative to counting measure on partitions and probability Haar measure is $\dim(\mathrm{Sp}_\lambda)\dim(V_\lambda^d)\Delta_\lambda(U^\dagger\rho U)$, combining source equations (8), (9), and (11). This removes division by a zero Schur probability without excluding singular states.
-- source:
--   Efficient quantum tomography, arXiv:1508.01907v2, Theorem 1.2, PDF p. 2. https://arxiv.org/abs/1508.01907v2 . PDF SHA-256: 8c640d5af5da6b0eb1a95185265f9e836b9bfd9a06cfc99e89753470c1eb066a.

import Definitions.Def_QAlgorithms_Defs_KeylTomography
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapL03

/-- O'Donnell and Wright, *Efficient quantum tomography*, arXiv:1508.01907v2,
Theorem 1.2 (PDF p.2), with the public two-stage measurement of pp.6–8.
The POVM is chosen before the unknown density matrix; its Born law is the computed
joint Schur–Weyl/Keyl law. The squared Frobenius risk is at most `(4*d-3)/n`.
Singular density matrices are included. The joint density uses (8), (9), and (11),
and the right-hand side of (10), avoiding its misplaced scalar inside the
degree-n representation on the left-hand side (PDF p.8). No change to Theorem 1.2
is made. No runtime, rank, accuracy, or normalization assumption is added. -/
theorem keyl_expectedSquaredFrobeniusError
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∃ measurement : Measurements.OperatorPOVM (Fin n → Fin d)
        (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ),
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho),
        Measurements.bornLaw measurement (piKron n rho)
            (Tomography.tensorDensity rho density n) =
          Tomography.keylJointLaw hd hn rho density ∧
        Tomography.keylSquaredRisk hd hn rho density ≤
          ENNReal.ofReal (((4 : ℝ) * d - 3) / n) := by sorry

end QAlgorithms.Papers.RoadmapL03
