-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_isotropic_smooth_optimizer
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.isotropic_smooth_optimizer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:35:16.922109+00:00
-- url     : https://prove2.me/theorems/2a86650e-b0e1-4cf9-8bac-6ff6105f869e
-- title:
--   Isotropic block form in the smooth max problem
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   SEPP consists of actual completely positive trace-preserving maps that send every fully separable state to a fully separable state. The resource $\Psi_M$ is a rank-$M$ maximally entangled state shared by the first two parties, with one-dimensional resource registers at the remaining parties; every positive integer $M$ is allowed.
--
--   Here $E_{\max}(\alpha)=\inf_{\sigma\in\mathcal S}\inf\{\log_2 s:\alpha\le s\sigma\}$ and $E_{\max}^{\varepsilon}(\alpha)=\min\{E_{\max}(\beta):\beta\text{ is normalized},\ F(\beta,\alpha)\ge1-\varepsilon\}$.
--
--   Fix any integer $K\ge2$ and any $\varepsilon>0$. There exist normalized states $\rho_\varepsilon,\theta$ on $H$ and a real number $\lambda$ with $0\le\lambda\le1$, $\lambda\le\varepsilon$, and $F(\rho,\rho_\varepsilon)\ge1-\varepsilon$, such that the normalized state
--
--   $$
--   \mu_\varepsilon=(1-\lambda)\rho_\varepsilon\otimes\Psi_K+
--   \lambda\theta\otimes\frac{I-\Psi_K}{K^2-1}
--   $$
--
--   satisfies
--
--   $$
--   E_{\max}(\mu_\varepsilon)\le E_{\max}^{\varepsilon}(\rho\otimes\Psi_K).
--   $$
--
--   The resource tensor product groups each party's original and resource registers. This gives a block-structured state with the required entanglement bound.
--
--   **Formalization Note** The proof uses a previously specified $K$, so it is fixed before the witnesses. The restriction $K\ge2$ prevents division by zero. The printed comparison $(1-\lambda)\ge F(\rho,\rho_\varepsilon)$ is not imposed; the correct joint fidelity is $(1-\lambda)F(\rho,\rho_\varepsilon)$.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 5, Lemma 3, Eqs.(36)–(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF p.5, Lemma 3, Eqs.(36)--(37),(40): specified K >= 2, with normalized blocks.
The K=1 complementary-block singularity is excluded. The proof's erroneous comparison
(1-lambda) >= F(rho,rho_eps) is not imposed. -/
theorem isotropic_smooth_optimizer {m : ℕ} (H : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) (eps : ℝ) (heps : 0 < eps)
    (K : ℕ+) (hK : 2 ≤ (K : ℕ)) :
    ∃ lam : ℝ, ∃ rhoE theta : MultipartiteOperator H,
      IsDensityMatrix rhoE ∧ IsDensityMatrix theta ∧
      0 ≤ lam ∧ lam ≤ 1 ∧ lam ≤ eps ∧ 1 - eps ≤ fidelity rho rhoE ∧
      IsDensityMatrix (isotropicMixture K lam rhoE theta) ∧
      maxEntanglement (isotropicMixture K lam rhoE theta) ≤
        fidelitySmoothMaxEntanglement (partyTensor rho (mes m K)) eps := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
