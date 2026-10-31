-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_choi_schatten_identity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.choi_schatten_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:58:04.810889+00:00
-- url     : https://prove2.me/theorems/72616bb5-a0a9-4b03-9dc3-04dfa097a1b3
-- title:
--   Choi and Schatten representation of sandwiched divergence
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   Write $\Gamma^{\mathcal N}_{AB}=(\operatorname{id}_A\otimes\mathcal N)(|\Gamma\rangle\langle\Gamma|)$, where $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$ is unnormalized, and $\Omega^{\mathcal N}(\rho)=(\rho^{1/2}\otimes I_B)\Gamma^{\mathcal N}_{AB}(\rho^{1/2}\otimes I_B)$. Its reference marginal is $\rho$ and its channel-input marginal is $\rho^{\mathsf T}$. Define $\widetilde I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ over all normalized densities. The finite attained extrema are retained as conclusions in the minimax statement.
--
--   Let $\mathcal N$ be CPTP and $\rho_A,\sigma_B$ be densities. Write $\|X\|_\alpha=(\operatorname{Tr}|X|^\alpha)^{1/\alpha}$ for the Schatten norm. Define $F_\alpha(\mathcal N,\rho,\sigma)$ to be
--
--   $$\left\|(\Gamma^{\mathcal N})^{1/2}\bigl(\rho^{1/\alpha}\otimes\sigma^{(1-\alpha)/\alpha}\bigr)(\Gamma^{\mathcal N})^{1/2}\right\|_\alpha$$
--
--   when $\operatorname{supp}\Omega^{\mathcal N}(\rho)\subseteq\operatorname{supp}(\rho\otimes\sigma)$, and $+\infty$ otherwise. Then
--
--   $$\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)=\frac\alpha{\alpha-1}\log_2 F_\alpha(\mathcal N,\rho,\sigma).$$
--
--   The unsupported branch has both $F_\alpha=+\infty$ and divergence $+\infty$. This representation relates the channel objective to operator norms while preserving singular comparisons.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 10, Lemma 3: Choi/Schatten form of sandwiched divergence, (5.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P15

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Intakenext100.P15

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- These are pinned accepted definitions, not other chunks from the current run.

open QAlgorithms.Papers.Independent.Bridge50.P43 (NormalizedDensity payoff)

open QAlgorithms.Papers.Independent.Dependency50.P09 (Divergence logExt sandwichedD petzD)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower SupportIncluded stateRelative channelPower diamond)

/-- PDF p.10, Lemma 3, (5.1). Includes both the finite compatible branch and infinity
on support failure, rather than silently replacing a negative power by a pseudoinverse. -/
theorem choi_schatten_identity
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (alpha : ℝ) (ha : 1 < alpha) (rho : NormalizedDensity A) (sigma : NormalizedDensity B) :
    sandwichedD alpha (eaChoiOutput N rho.1) (Matrix.kronecker rho.1 sigma.1) =
      ((alpha / (alpha - 1) : ℝ) : EReal) * logExt (choiObjective alpha N rho.1 sigma.1) ∧
    (¬ SupportIncluded (eaChoiOutput N rho.1) (Matrix.kronecker rho.1 sigma.1) →
      choiObjective alpha N rho.1 sigma.1 = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
