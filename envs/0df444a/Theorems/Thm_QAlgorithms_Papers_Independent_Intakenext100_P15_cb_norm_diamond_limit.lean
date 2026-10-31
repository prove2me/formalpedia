-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_cb_norm_diamond_limit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.cb_norm_diamond_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:08:51.6135+00:00
-- url     : https://prove2.me/theorems/45ced2e2-8fd2-44fe-b3fb-108283e9c1ff
-- title:
--   The completely bounded one-to-alpha norm approaches the diamond norm
-- statement:
--   Let $\mathcal M:\mathcal B(A')\to\mathcal B(B)$ be a complex-linear completely positive map on nonzero finite-dimensional spaces, without a trace-preserving requirement. Its Choi matrix uses the unnormalized vector $|\Gamma\rangle=\sum_i|i\rangle|i\rangle$. For $\alpha\ge1$, let
--
--   $$b_\alpha(\mathcal M)=\sup_{\rho_A}\left\|(\rho_A^{1/(2\alpha)}\otimes I_B)\Gamma^{\mathcal M}_{AB}(\rho_A^{1/(2\alpha)}\otimes I_B)\right\|_\alpha,$$
--
--   where $\rho_A$ ranges over all density operators and $\|\cdot\|_\alpha$ is the Schatten norm. Each supremum is attained. Define the unhalved diamond norm by $\|\mathcal M\|_\diamond=\sup_{\|X\|_1\le1}\|(\operatorname{id}_A\otimes\mathcal M)(X)\|_1$, where $X$ ranges over arbitrary matrices on $A\otimes A'$ and the reference is isomorphic to the input. Then
--
--   $$\lim_{\alpha\downarrow1}b_\alpha(\mathcal M)=b_1(\mathcal M)=\|\mathcal M\|_\diamond.$$
--
--   This relates the positive-Choi one-to-alpha quantity to the stabilized trace norm at its endpoint.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 3, Unnumbered observation: CB 1→α norm tends to the diamond norm

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

/-- PDF p.3, unnumbered observation following (2.2): CB 1-to-alpha tends to
the diamond norm for CP maps, including maps that are not trace preserving.
Attainment witnesses elaborate the maximum in the defining equation (2.1). -/
theorem cb_norm_diamond_limit
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (M : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hM : QAlgorithms.Entanglement.IsCompletelyPositive M) :
    Tendsto (fun alpha : ℝ => cbOneAlpha alpha M) (𝓝[>] (1 : ℝ))
      (𝓝 ((diamond M : ℝ) : EReal)) ∧
    cbOneAlpha 1 M = (diamond M : EReal) ∧
    (∀ alpha : ℝ, 1 ≤ alpha → ∃ rho : NormalizedDensity A,
      let S := Matrix.kronecker (supportPower rho.1 (1 / (2 * alpha))) (1 : Matrix B B ℂ)
      cbOneAlpha alpha M = (schatten alpha (S * choi M * S) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
