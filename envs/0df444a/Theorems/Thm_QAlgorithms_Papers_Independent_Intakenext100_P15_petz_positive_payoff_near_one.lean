-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_petz_positive_payoff_near_one
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.petz_positive_payoff_near_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:08:06.99398+00:00
-- url     : https://prove2.me/theorems/47f07d6a-23fc-4683-87ac-637b4f7fa48d
-- title:
--   Positive Petz payoff uniformly near order one
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   Write $\Gamma^{\mathcal N}_{AB}=(\operatorname{id}_A\otimes\mathcal N)(|\Gamma\rangle\langle\Gamma|)$, where $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$ is unnormalized, and $\Omega^{\mathcal N}(\rho)=(\rho^{1/2}\otimes I_B)\Gamma^{\mathcal N}_{AB}(\rho^{1/2}\otimes I_B)$. Its reference marginal is $\rho$ and its channel-input marginal is $\rho^{\mathsf T}$. Define $\widetilde I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ over all normalized densities. The finite attained extrema are retained as conclusions in the minimax statement.
--
--   Define $I(\mathcal N)=\sup_\rho\inf_\sigma D(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ with Umegaki divergence, and $I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$. For CPTP $\mathcal N$ and real $R>I(\mathcal N)$,
--
--   $$\exists\beta\in(1,2),\quad\forall\alpha\in(1,\beta),\qquad \frac{\alpha-1}{\alpha}(R-I_\alpha(\mathcal N))>0.$$
--
--   For every order in this neighborhood the Petz channel supremum is finite and attained by an input density. The neighborhood depends on $\mathcal N,R$ and is uniform over all input states. Restricting it within order two preserves the near-one claim and avoids the unrestricted maximum defect of (6.6).
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 17, Lemma 10: a positive Petz payoff near one, (6.43)

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

/-- PDF p.17, Lemma 10, (6.43). The Petz channel information is only used in
a right neighborhood of one, chosen within alpha<2. Its finite maximum is attained
in that neighborhood; no all-order Petz maximum is asserted. -/
theorem petz_positive_payoff_near_one
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (R : ℝ) (hR : channelInfo stateRelative N < (R : EReal)) :
    ∃ beta : ℝ, 1 < beta ∧ beta < 2 ∧ ∀ alpha : ℝ, 1 < alpha → alpha < beta →
      0 < payoff alpha R (channelInfo (petzD alpha) N) ∧
      ∃ (v : ℝ) (rho : NormalizedDensity A),
        channelInfo (petzD alpha) N = (v : EReal) ∧ inputInfo (petzD alpha) N rho = (v : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
