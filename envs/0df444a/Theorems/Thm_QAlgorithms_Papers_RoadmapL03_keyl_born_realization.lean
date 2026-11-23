-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_born_realization
-- name    : QAlgorithms.Papers.RoadmapL03.keyl_born_realization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T11:40:29.890639+00:00
-- url     : https://prove2.me/theorems/0ebd1cc8-b7cf-44a4-ac31-4e8f8d7e0fb4
-- title:
--   Keyl's two-stage tomography law is a Born law
-- statement:
--   Let $d,n\ge1$. There is a single operator-valued measure (POVM) $M$ on $n$ copies of $\mathbb C^d$, with outcomes $(\lambda,U)$ where $\lambda$ is a partition of $n$ with at most $d$ rows and $U\in U(d)$. It is fixed before the unknown state is supplied and realizes Keyl's two-stage tomography law. For every density matrix $\rho$ on $\mathbb C^d$ and every measurable outcome event $B$,
--
--   $$\operatorname{tr}\big(M(B)\,\rho^{\otimes n}\big)=\sum_{\lambda}\int_{\{U:(\lambda,U)\in B\}}\dim(\mathrm{Sp}_\lambda)\,\dim(V^d_\lambda)\,\Delta_\lambda(U^\dagger\rho U)\,dU .$$
--
--   Here $dU$ is the probability Haar measure, $\mathrm{Sp}_\lambda$ is the Specht module, $V^d_\lambda$ is the Schur module, and $\Delta_\lambda(Z)=\prod_k\operatorname{pm}_k(Z)^{\lambda_k-\lambda_{k+1}}$ is Keyl's generalized power. The right-hand side is the joint law of the outcome of weak Schur sampling, $\lambda\sim\mathrm{SW}^n(\alpha)$, followed by Keyl's highest-weight measurement $U\sim\mathrm K_\lambda(\rho)$ (O'Donnell–Wright, equations (8)–(11)).
--
--   The theorem certifies that this joint law is a genuine Born law of one physically realizable measurement, including for singular $\rho$. It is the measurement half of O'Donnell–Wright's Theorem 1.2.
--
--   **Formalization Note.** The joint law is `Tomography.keylJointLaw`, a density with respect to counting measure on shapes times probability Haar measure. Equality of measures is equality on all measurable sets of the product $\sigma$-algebra.
-- source:
--   R. O'Donnell and J. Wright, Efficient quantum tomography, arXiv:1508.01907v2, Section 4 (pp. 6-8), Keyl's measurement and equations (8)-(11); Theorem 1.2 (p. 2). https://arxiv.org/abs/1508.01907v2

import Definitions.Def_QAlgorithms_Defs_KeylTomography
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapL03

theorem keyl_born_realization (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∃ measurement : Measurements.OperatorPOVM (Fin n → Fin d)
        (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ),
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho),
        Measurements.bornLaw measurement (piKron n rho)
            (Tomography.tensorDensity rho density n) =
          Tomography.keylJointLaw hd hn rho density := by sorry

end QAlgorithms.Papers.RoadmapL03
