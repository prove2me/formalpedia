-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_singleUsePareto
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.singleUsePareto
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:34:14.517328+00:00
-- url     : https://prove2.me/theorems/d724ca98-091a-43e6-ae1f-dea27001f904
-- title:
--   Single-letterization reduces supporting-surface optimization to one channel use
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   For fixed $\lambda,\mu\ge0$, define the attained one-use optimum
--   $$
--   P_{\lambda,\mu}(\mathcal N)=\max_\sigma\bigl\{I(XY;B)_\sigma+\lambda[I(Y;B|X)_\sigma-I(Y;E|X)_\sigma]+\mu[I(XY;B)_\sigma-I(Y;E|X)_\sigma]\bigr\}.
--   $$
--
--   Assume that for every $\lambda,\mu\ge0$ the regularized formula single-letterizes:
--   $$
--   \lim_{n\to\infty}\frac1nP_{\lambda,\mu}(\mathcal N^{\otimes n})=P_{\lambda,\mu}(\mathcal N).
--   $$
--   Then, for every such pair of weights,
--   $$
--   \max_{(R,P,S)\in\mathcal C(\mathcal N)}\{R+P+\lambda(P+S)+\mu(R+P+S)\}=P_{\lambda,\mu}(\mathcal N).
--   $$
--   Thus the nonnegative supporting directions of the Pareto trade-off surface require a single-use ensemble optimization. No assertion of efficient numerical optimization is made.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 10, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P24

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E] [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- Theorem 2, PDF p.10: under single-letterization in every nonnegative direction,
the operational region's supporting surface is computed by one-use optimization.
This is a geometric claim and asserts neither numerical tractability nor an optimal code. -/
theorem singleUsePareto (V : Dilation I B E) (hV : PhysicalDilation V)
    (hSingle : ∀ lam mu : ℝ, 0 ≤ lam → 0 ≤ mu →
      ∃ v, IsGreatest (values (dynamicObjective V lam mu)) v ∧ RegularizesTo V lam mu v) :
    ∀ lam mu : ℝ, 0 ≤ lam → 0 ≤ mu →
      EqualMax (values (dynamicObjective V lam mu)) (rpsSupport lam mu '' privateDynamicRegion V) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
