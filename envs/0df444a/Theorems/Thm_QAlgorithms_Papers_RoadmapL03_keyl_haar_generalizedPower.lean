-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_haar_generalizedPower
-- name    : QAlgorithms.Papers.RoadmapL03.keyl_haar_generalizedPower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T11:26:23.005093+00:00
-- url     : https://prove2.me/theorems/006d8de1-de60-4950-b0ba-46ee88866b40
-- title:
--   Haar average of Keyl's generalized power
-- statement:
--   Let $d,n\ge 0$ and let $\lambda$ be a partition of $n$ with at most $d$ rows. Let $V^d_\lambda\subseteq(\mathbb C^d)^{\otimes n}$ be the Schur module of $\lambda$ (the image of the Young symmetrizer acting on tensor space), and let $\pi_\lambda(A)$ be the action of a $d\times d$ matrix $A$ on it, i.e. the compression of $A^{\otimes n}$ to $V^d_\lambda$. For a $d\times d$ matrix $Z$, Keyl's generalized power is
--
--   $$\Delta_\lambda(Z)=\prod_{k=1}^{d}\operatorname{pm}_k(Z)^{\lambda_k-\lambda_{k+1}},$$
--
--   where $\operatorname{pm}_k(Z)$ is the $k$-th leading principal minor and $\lambda_{d+1}=0$.
--
--   **Theorem.** For every complex $d\times d$ matrix $A$,
--
--   $$\int_{U(d)}\Delta_\lambda\big(U^\dagger A U\big)\,dU=\frac{\operatorname{tr}\pi_\lambda(A)}{\dim V^d_\lambda},$$
--
--   where $dU$ is the probability Haar measure on the unitary group $U(d)$.
--
--   For a density matrix $\rho$ with spectrum $\alpha$, the right-hand side equals $s_\lambda(\alpha)/s_\lambda(1,\dots,1)=\Phi_\lambda(\alpha)$, the normalized Schur polynomial. In this form the identity is equation (12) of O'Donnell and Wright. It is the normalization identity behind Keyl's covariant measurement: it shows that the second-stage operators integrate to the identity on each Schur module, and it gives the Haar integrals of generalized powers that appear in the risk analysis.
--
--   **Formalization Note.** The identity is stated for arbitrary complex matrices, not only density matrices. $\operatorname{tr}\pi_\lambda(A)$ is the trace of the linear map `Schur.polynomialRepresentation lambda A` on `Schur.schurModule lambda`, and $\Delta_\lambda$ is `Tomography.keylGeneralizedPower`.
-- source:
--   R. O'Donnell and J. Wright, Efficient quantum tomography, arXiv:1508.01907v2, Section 4.1, eq. (12) (E_{U~U(d)} Delta_lambda(U^dagger rho U) = Phi_lambda(alpha)), together with Notation 4.1 and Keyl's identity <T_lambda|pi_lambda(Z)|T_lambda> = Delta_lambda(Z) (M. Keyl, Quantum state estimation and large deviations, Rev. Math. Phys. 18 (2006) 19-60, eq. (141)). https://arxiv.org/abs/1508.01907v2

import Definitions.Def_QAlgorithms_Defs_KeylTomography
set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.RoadmapL03

theorem keyl_haar_generalizedPower {d n : ℕ} (lambda : Schur.Partition d n)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ∫ U, Tomography.keylGeneralizedPower lambda
        (star (U : Matrix (Fin d) (Fin d) ℂ) * A * (U : Matrix (Fin d) (Fin d) ℂ)) ∂(Schur.unitaryHaar d) =
      LinearMap.trace ℂ (Schur.schurModule lambda) (Schur.polynomialRepresentation lambda A) /
        (Module.finrank ℂ (Schur.schurModule lambda) : ℂ) := by sorry

end QAlgorithms.Papers.RoadmapL03
