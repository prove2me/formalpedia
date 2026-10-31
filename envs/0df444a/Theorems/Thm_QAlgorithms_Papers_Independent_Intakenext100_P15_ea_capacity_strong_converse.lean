-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_ea_capacity_strong_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.ea_capacity_strong_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:55:54.507069+00:00
-- url     : https://prove2.me/theorems/2f87a9ca-105d-4cf5-902a-e714ff707265
-- title:
--   Theorem 11: exponential strong converse for entanglement-assisted capacity
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   Write $\Gamma^{\mathcal N}_{AB}=(\operatorname{id}_A\otimes\mathcal N)(|\Gamma\rangle\langle\Gamma|)$, where $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$ is unnormalized, and $\Omega^{\mathcal N}(\rho)=(\rho^{1/2}\otimes I_B)\Gamma^{\mathcal N}_{AB}(\rho^{1/2}\otimes I_B)$. Its reference marginal is $\rho$ and its channel-input marginal is $\rho^{\mathsf T}$. Define $\widetilde I_\alpha(\mathcal N)=\sup_\rho\inf_\sigma\widetilde D_\alpha(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$ over all normalized densities. The finite attained extrema are retained as conclusions in the minimax statement.
--
--   An $n$-use parallel entanglement-assisted classical code has $n\ge1$, an integer $M\ge1$ of uniform messages, an arbitrary finite message-independent shared bipartite density $\Psi_{T_AT_B}$, message-dependent local CPTP encoders $\mathcal E_m:T_A\to A'^n$, and a joint POVM $\{\Lambda_m\}_{m=1}^M$ on $B^nT_B$. Its rate is $r_C=\log_2(M)/n$, and its average success probability is $p_{\rm succ}=M^{-1}\sum_m\operatorname{Tr}[\Lambda_m(\mathcal N^{\otimes n}\otimes\operatorname{id}_{T_B})(\mathcal E_m\otimes\operatorname{id}_{T_B})(\Psi)]$.
--
--   Let $I(\mathcal N)=\sup_\rho\inf_\sigma D(\Omega^{\mathcal N}(\rho)\Vert\rho\otimes\sigma)$, with $D$ the Umegaki divergence in bits. This value is finite and its defining maximum and inner minimum have attaining density witnesses. For every real $R>I(\mathcal N)$ there is $c>0$, depending only on $\mathcal N$ and $R$, such that
--
--   $$\forall n\ge1,\quad\forall C\text{ with }r_C\ge R,\qquad p_{\rm succ}(C,\mathcal N^{\otimes n})\le 2^{-cn}.$$
--
--   Consequently every such sequence of parallel codes has success tending exponentially to zero.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 17, Theorem 11 (Strong converse for EA capacity); abstract seed

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

/-- PDF p.17, Theorem 11. One positive exponent works for every block length,
message count, ancilla dimension and parallel EA code with rate at least R.
The positive-block formulation implies exponential decay for every such sequence. -/
theorem ea_capacity_strong_converse
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (R : ℝ) (hR : channelInfo stateRelative N < (R : EReal)) :
    (∃ (v : ℝ) (rho0 : NormalizedDensity A) (sigma0 : NormalizedDensity B),
      channelInfo stateRelative N = (v : EReal) ∧ inputInfo stateRelative N rho0 = (v : EReal) ∧
      stateRelative (eaChoiOutput N rho0.1) (Matrix.kronecker rho0.1 sigma0.1) = (v : EReal)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ C : ParallelEACode A B n, R ≤ parallelEARate C →
      parallelEASuccess N C ≤ Real.rpow 2 (-(n : ℝ) * c)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
