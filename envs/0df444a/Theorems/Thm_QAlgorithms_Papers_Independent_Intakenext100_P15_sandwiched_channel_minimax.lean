-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_sandwiched_channel_minimax
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.sandwiched_channel_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:03:11.039613+00:00
-- url     : https://prove2.me/theorems/3514564d-e442-4afa-8f31-7381c24dbc1c
-- title:
--   Sandwiched channel minimax with attained extrema
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   Write $\Gamma^{\mathcal N}_{AB}=(\operatorname{id}_A\otimes\mathcal N)(|\Gamma\rangle\langle\Gamma|)$, where $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$ is unnormalized, and $\Omega^{\mathcal N}(\rho)=(\rho^{1/2}\otimes I_B)\Gamma^{\mathcal N}_{AB}(\rho^{1/2}\otimes I_B)$. Its reference marginal is $\rho$ and its channel-input marginal is $\rho^{\mathsf T}$. Define $\widetilde I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ over all normalized densities. The finite attained extrema are retained as conclusions in the minimax statement.
--
--   For every CPTP $\mathcal N$ and real $\alpha>1$,
--
--   $$\widetilde I_\alpha(\mathcal N)=\inf_{\sigma_B}\sup_{\rho_A}\widetilde D_\alpha(\Omega^{\mathcal N}(\rho_A)\Vert\rho_A\otimes\sigma_B).$$
--
--   Both optimizations range over all density operators. There are a real $v$ and densities $\rho_0,\sigma_0$ with $v=\widetilde I_\alpha(\mathcal N)$ and
--
--   $$\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma_0)\le v=\widetilde D_\alpha(\Omega^{\mathcal N}(\rho_0)\Vert\rho_0\otimes\sigma_0)\le\widetilde D_\alpha(\Omega^{\mathcal N}(\rho_0)\Vert\rho_0\otimes\sigma)$$
--
--   for every density $\rho,\sigma$. Every fixed-input inner infimum and every fixed-comparison inner supremum also has an attaining witness, allowing infinite fixed-comparison suprema. Thus the displayed outer extrema and the original channel maximum are attained. This is the exchange of minimum and maximum used in channel additivity.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 11, Lemma 5: sandwiched channel minimax identity, (5.16)

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

/-- PDF pp.11--12, Lemma 5, (5.16). Equality, finite value, saddle witnesses,
and attainment of every inner minimum/maximum elaborate the printed min/max. -/
theorem sandwiched_channel_minimax
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (alpha : ℝ) (ha : 1 < alpha) :
    channelInfo (sandwichedD alpha) N =
      (⨅ sigma : NormalizedDensity B, ⨆ rho : NormalizedDensity A,
        sandwichedD alpha (eaChoiOutput N rho.1) (Matrix.kronecker rho.1 sigma.1)) ∧
    (∃ (v : ℝ) (rho0 : NormalizedDensity A) (sigma0 : NormalizedDensity B),
      channelInfo (sandwichedD alpha) N = (v : EReal) ∧
      sandwichedD alpha (eaChoiOutput N rho0.1) (Matrix.kronecker rho0.1 sigma0.1) = (v : EReal) ∧
      (∀ rho : NormalizedDensity A,
        sandwichedD alpha (eaChoiOutput N rho.1) (Matrix.kronecker rho.1 sigma0.1) ≤ (v : EReal)) ∧
      (∀ sigma : NormalizedDensity B,
        (v : EReal) ≤ sandwichedD alpha (eaChoiOutput N rho0.1) (Matrix.kronecker rho0.1 sigma.1))) ∧
    (∀ rho : NormalizedDensity A, ∃ sigma : NormalizedDensity B,
      sandwichedD alpha (eaChoiOutput N rho.1) (Matrix.kronecker rho.1 sigma.1) =
        inputInfo (sandwichedD alpha) N rho) ∧
    (∀ sigma : NormalizedDensity B, ∃ rho0 : NormalizedDensity A,
      sandwichedD alpha (eaChoiOutput N rho0.1) (Matrix.kronecker rho0.1 sigma.1) =
        ⨆ rho : NormalizedDensity A,
          sandwichedD alpha (eaChoiOutput N rho.1) (Matrix.kronecker rho.1 sigma.1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
