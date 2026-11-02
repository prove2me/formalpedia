-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P41_entropy_firstOrder
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P41.entropy_firstOrder
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:54:03.375419+00:00
-- url     : https://prove2.me/theorems/87983b3b-a058-4f1e-bc15-9278f6635b74
-- title:
--   First-order entropy response on a regulated finite occupied support
-- statement:
--   Let $\rho(t)=\rho_0+t\rho_1$ be a density operator on an arbitrary finite occupied-support realization of a regulated system. Assume $\rho_0\ge0$, $\operatorname{Tr}\rho_0=1$, $\rho_1$ is Hermitian, $\operatorname{Tr}\rho_1=0$, and $\operatorname{im}\rho_1\subseteq\operatorname{im}\rho_0$. For all sufficiently small real $t$ of either sign, assume $\rho(t)$ remains positive and has the same occupied support as $\rho_0$. For every fixed real $\alpha>0$, $\alpha\ne1$, the Renyi entropy $S_\alpha(\rho)=\log\operatorname{Tr}(\rho^\alpha)/(1-\alpha)$ and von Neumann entropy $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$, both in nats, satisfy
--
--   $$
--   S_\alpha(\rho(t))=S_\alpha(\rho_0)+t\frac{\alpha}{1-\alpha}\frac{\operatorname{Tr}(\rho_1\rho_0^{\alpha-1})}{\operatorname{Tr}(\rho_0^\alpha)}+O(t^2),
--   \qquad
--   S(\rho(t))=S(\rho_0)-t\operatorname{Tr}(\rho_1\log\rho_0)+O(t^2).
--   $$
--
--   Powers and logarithms are taken on the occupied support. Each remainder is two-sided as $t\to0$, with constants allowed to depend on the fixed state, perturbation and order. These responses compare ordinary and Renyi entropy under a support-preserving perturbation.
--
--   **Formalization Note** The index type is arbitrary and finite, rather than a prescribed matrix dimension. This is the plan's regulated finite-rank interpretation; it does not assert an infinite-rank trace-class differentiability theorem.
-- source:
--   Entanglement Renyi entropies in holographic theories, arXiv:1006.0047v3, PDF p. 7, §2.2, (2.8)–(2.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P41

namespace QAlgorithms.Papers.Independent.Intakethird100.P41

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open scoped Topology

/-- PDF p.7, (2.9)-(2.10): both first-order entropy responses, with quadratic
remainders, for the regulated finite-rank interpretation. The dimension is arbitrary,
zero eigenvalues are allowed, and no commutation hypothesis is imposed on rho0 and rho1.
The infinite-rank interpretation requires additional trace/differentiability domains. -/
theorem entropy_firstOrder {I : Type*} [Fintype I] [DecidableEq I]
    (rho0 rho1 : Matrix I I ℂ) (hpert : IsSupportPreservingPerturbation rho0 rho1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Asymptotics.IsBigO (𝓝 (0 : ℝ))
      (fun t : ℝ => regulatedRenyiNats a (densityPerturbation rho0 rho1 t) -
        regulatedRenyiNats a rho0 - t * (a / (1 - a) *
          (rho1 * occupiedPower (a - 1) rho0).trace.re /
            (occupiedPower a rho0).trace.re))
      (fun t : ℝ => t ^ 2) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℝ))
      (fun t : ℝ => entropy (densityPerturbation rho0 rho1 t) -
        entropy rho0 + t * (rho1 * cfc Real.log rho0).trace.re)
      (fun t : ℝ => t ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P41
