-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_singleletter_success_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.singleletter_success_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:04:41.12299+00:00
-- url     : https://prove2.me/theorems/9187d302-358e-40ad-b688-1a033bf08b49
-- title:
--   Single-letter lower bound on the strong-converse exponent
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   Write $\Gamma^{\mathcal N}_{AB}=(\operatorname{id}_A\otimes\mathcal N)(|\Gamma\rangle\langle\Gamma|)$, where $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$ is unnormalized, and $\Omega^{\mathcal N}(\rho)=(\rho^{1/2}\otimes I_B)\Gamma^{\mathcal N}_{AB}(\rho^{1/2}\otimes I_B)$. Its reference marginal is $\rho$ and its channel-input marginal is $\rho^{\mathsf T}$. Define $\widetilde I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ over all normalized densities. The finite attained extrema are retained as conclusions in the minimax statement.
--
--   An $n$-use parallel entanglement-assisted classical code has $n\ge1$, an integer $M\ge1$ of uniform messages, an arbitrary finite message-independent shared bipartite density $\Psi_{T_AT_B}$, message-dependent local CPTP encoders $\mathcal E_m:T_A\to A'^n$, and a joint POVM $\{\Lambda_m\}_{m=1}^M$ on $B^nT_B$. Its rate is $r_C=\log_2(M)/n$, and its average success probability is $p_{\rm succ}=M^{-1}\sum_m\operatorname{Tr}[\Lambda_m(\mathcal N^{\otimes n}\otimes\operatorname{id}_{T_B})(\mathcal E_m\otimes\operatorname{id}_{T_B})(\Psi)]$.
--
--   For every real rate lower bound $R\le r_C$,
--
--   $$p_{\rm succ}\le 2^{-n E(R,\mathcal N)},\qquad E(R,\mathcal N)=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}(R-\widetilde I_\alpha(\mathcal N)).$$
--
--   The supremum covers the entire order interval $(1,\infty)$. Exponentiation uses extended endpoints $2^{-\infty}=0$ and $2^{+\infty}=+\infty$. This finite-block inequality supplies a lower bound on the decay exponent of every code; it does not identify an optimal exponent.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 13, Unnumbered single-letter EA strong-converse exponent bound, (6.1)/(2.20)

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

/-- PDF pp.6,13, (2.20),(6.1). An upper bound on parallelEASuccess of each code, rather than
an assertion identifying the optimal strong-converse exponent. -/
theorem singleletter_success_bound
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (n : ℕ) (hn : 1 ≤ n) (C : ParallelEACode A B n) (R : ℝ) (hR : R ≤ parallelEARate C) :
    ENNReal.ofReal (parallelEASuccess N C) ≤ expBits
      (-((n : ℝ) : EReal) *
        ⨆ alpha : {a : ℝ // 1 < a}, payoff alpha.1 R (channelInfo (sandwichedD alpha.1) N)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
