-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_choi_objective_curvature
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.choi_objective_curvature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:58:53.289275+00:00
-- url     : https://prove2.me/theorems/89e39fcc-d88a-4300-9a63-82a15aa0bf44
-- title:
--   Separate concavity and convexity of the Choi norm objective
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   Write $\Gamma^{\mathcal N}_{AB}=(\operatorname{id}_A\otimes\mathcal N)(|\Gamma\rangle\langle\Gamma|)$, where $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$ is unnormalized, and $\Omega^{\mathcal N}(\rho)=(\rho^{1/2}\otimes I_B)\Gamma^{\mathcal N}_{AB}(\rho^{1/2}\otimes I_B)$. Its reference marginal is $\rho$ and its channel-input marginal is $\rho^{\mathsf T}$. Define $\widetilde I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ over all normalized densities. The finite attained extrema are retained as conclusions in the minimax statement.
--
--   For CPTP $\mathcal N$ define $F_\alpha(\rho,\sigma)=\| (\Gamma^{\mathcal N})^{1/2}(\rho^{1/\alpha}\otimes\sigma^{(1-\alpha)/\alpha})(\Gamma^{\mathcal N})^{1/2}\|_\alpha$ on support-compatible pairs and $+\infty$ otherwise. For any density endpoints and $0<t<1$,
--
--   $$tF_\alpha(\rho_0,\sigma)+(1-t)F_\alpha(\rho_1,\sigma)\le F_\alpha(t\rho_0+(1-t)\rho_1,\sigma),$$
--
--   $$F_\alpha(\rho,t\sigma_0+(1-t)\sigma_1)\le tF_\alpha(\rho,\sigma_0)+(1-t)F_\alpha(\rho,\sigma_1).$$
--
--   At $t=0,1$, the respective mixtures equal their selected endpoints; these four equalities are stated separately. The result supplies separate curvature of the norm objective for minimax optimization.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 11, Lemma 4: separate concavity and convexity, (5.8)

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

/-- PDF p.11, Lemma 4, (5.8). Separate concavity in rho and convexity in sigma.
Strict mixtures suffice together with the tautological endpoint equalities. -/
theorem choi_objective_curvature
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (alpha : ℝ) (ha : 1 < alpha) :
    (∀ (rho0 rho1 : NormalizedDensity A) (sigma : NormalizedDensity B) (t : ℝ), 0 < t → t < 1 →
      (t : EReal) * choiObjective alpha N rho0.1 sigma.1 +
        ((1 - t : ℝ) : EReal) * choiObjective alpha N rho1.1 sigma.1 ≤
      choiObjective alpha N (convexStateMix t rho0.1 rho1.1) sigma.1) ∧
    (∀ (rho : NormalizedDensity A) (sigma0 sigma1 : NormalizedDensity B) (t : ℝ), 0 < t → t < 1 →
      choiObjective alpha N rho.1 (convexStateMix t sigma0.1 sigma1.1) ≤
        (t : EReal) * choiObjective alpha N rho.1 sigma0.1 +
          ((1 - t : ℝ) : EReal) * choiObjective alpha N rho.1 sigma1.1) ∧
    (∀ (rho0 rho1 : NormalizedDensity A) (sigma : NormalizedDensity B),
      choiObjective alpha N (convexStateMix 0 rho0.1 rho1.1) sigma.1 = choiObjective alpha N rho1.1 sigma.1 ∧
      choiObjective alpha N (convexStateMix 1 rho0.1 rho1.1) sigma.1 = choiObjective alpha N rho0.1 sigma.1) ∧
    (∀ (rho : NormalizedDensity A) (sigma0 sigma1 : NormalizedDensity B),
      choiObjective alpha N rho.1 (convexStateMix 0 sigma0.1 sigma1.1) = choiObjective alpha N rho.1 sigma1.1 ∧
      choiObjective alpha N rho.1 (convexStateMix 1 sigma0.1 sigma1.1) = choiObjective alpha N rho.1 sigma0.1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
