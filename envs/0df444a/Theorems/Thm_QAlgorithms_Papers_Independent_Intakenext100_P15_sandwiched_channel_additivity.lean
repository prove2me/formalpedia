-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_sandwiched_channel_additivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.sandwiched_channel_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:04:01.870074+00:00
-- url     : https://prove2.me/theorems/295f5a45-c742-4123-8a4a-af02d3e31c14
-- title:
--   Additivity of sandwiched channel mutual information
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   Write $\Gamma^{\mathcal N}_{AB}=(\operatorname{id}_A\otimes\mathcal N)(|\Gamma\rangle\langle\Gamma|)$, where $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$ is unnormalized, and $\Omega^{\mathcal N}(\rho)=(\rho^{1/2}\otimes I_B)\Gamma^{\mathcal N}_{AB}(\rho^{1/2}\otimes I_B)$. Its reference marginal is $\rho$ and its channel-input marginal is $\rho^{\mathsf T}$. Define $\widetilde I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ over all normalized densities. The finite attained extrema are retained as conclusions in the minimax statement.
--
--   For arbitrary CPTP maps $\mathcal N_1:A'_1\to B_1$ and $\mathcal N_2:A'_2\to B_2$, and every $\alpha>1$,
--
--   $$\widetilde I_\alpha(\mathcal N_1\otimes\mathcal N_2)=\widetilde I_\alpha(\mathcal N_1)+\widetilde I_\alpha(\mathcal N_2).$$
--
--   The tensor-power specialization, for every integer $n\ge1$, is
--
--   $$\widetilde I_\alpha(\mathcal N_1^{\otimes n})=n\widetilde I_\alpha(\mathcal N_1).$$
--
--   Input and output dimensions may all differ. The joint optimization includes correlated states on both the reference inputs and comparison outputs. This additivity converts the multiletter converse into a single-letter bound.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 12, Lemma 6: additivity of sandwiched channel mutual information, (5.23)

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

/-- PDF pp.12--13, Lemma 6, (5.23). Joint optimizations include correlated inputs
and comparisons. The two channels may have four different nonzero dimensions. -/
theorem sandwiched_channel_additivity
    {A1 B1 A2 B2 : Type} [Fintype A1] [Fintype B1] [Fintype A2] [Fintype B2]
    [DecidableEq A1] [DecidableEq B1] [DecidableEq A2] [DecidableEq B2]
    [Nonempty A1] [Nonempty B1] [Nonempty A2] [Nonempty B2]
    (N1 : Superop A1 B1) (hN1 : IsChannel N1)
    (N2 : Superop A2 B2) (hN2 : IsChannel N2) (alpha : ℝ) (ha : 1 < alpha) :
    channelInfo (sandwichedD alpha) (unbundledTensorMap N1 N2) =
      channelInfo (sandwichedD alpha) N1 + channelInfo (sandwichedD alpha) N2 ∧
    (∀ n : ℕ, 1 ≤ n → channelInfo (sandwichedD alpha) (channelPower N1 n) =
      ((n : ℝ) : EReal) * channelInfo (sandwichedD alpha) N1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
