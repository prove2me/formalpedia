-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_logtrace_derivative_limit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.logtrace_derivative_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:07:13.88181+00:00
-- url     : https://prove2.me/theorems/fce17313-df87-469d-9de8-2df5705b4529
-- title:
--   Right derivative limit of the Petz log-trace function
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   For a bipartite density $\rho_{AB}$, let $\rho_A=\operatorname{Tr}_B\rho_{AB}$ and put $K_\alpha=\operatorname{Tr}_A[((\rho_A^{(1-\alpha)/2})\otimes I_B)\rho_{AB}^\alpha((\rho_A^{(1-\alpha)/2})\otimes I_B)]$, $Z_\alpha=\operatorname{Tr}K_\alpha^{1/\alpha}$, and $\sigma_B^*=K_\alpha^{1/\alpha}/Z_\alpha$. Partial-trace cyclicity gives $K_\alpha=\operatorname{Tr}_A[(\rho_A^{1-\alpha}\otimes I_B)\rho_{AB}^\alpha]$.
--
--   Put $f(\alpha)=\log_2 Z_\alpha$. This function is differentiable at every $\alpha>1$, and
--
--   $$\lim_{\alpha\downarrow1} f'(\alpha)=S(\rho_A)+S(\rho_B)-S(\rho_{AB})=I(A;B)_\rho,$$
--
--   where $\rho_B=\operatorname{Tr}_A\rho_{AB}$ and $S(\tau)=-\operatorname{Tr}(\tau\log_2\tau)$. The limit concerns the derivative, and approaches one from above. This identifies the first-order behavior used for positive converse payoffs.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 15, Lemma 9: derivative limit at order one, (6.25)

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

/-- PDF pp.15--16, Lemma 9, (6.25). The derivative approaches order one from
above; both the log-trace function and mutual information use base two. -/
theorem logtrace_derivative_limit
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (rho : NormalizedDensity (A × B)) :
    (∀ alpha : ℝ, 1 < alpha → DifferentiableAt ℝ (logTrace rho.1) alpha) ∧
    Tendsto (deriv (logTrace rho.1)) (𝓝[>] (1 : ℝ)) (𝓝 (ordinaryStateInfo rho.1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
