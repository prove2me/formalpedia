-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_antidegradableEBAdditivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.antidegradableEBAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:42:35.584426+00:00
-- url     : https://prove2.me/theorems/6852b58e-7d21-4d36-b5a8-d0460e0311ed
-- title:
--   Additivity for antidegradable and entanglement-breaking factors
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   For fixed $\lambda,\mu\ge0$, define the attained one-use optimum
--   $$
--   P_{\lambda,\mu}(\mathcal N)=\max_\sigma\bigl\{I(XY;B)_\sigma+\lambda[I(Y;B|X)_\sigma-I(Y;E|X)_\sigma]+\mu[I(XY;B)_\sigma-I(Y;E|X)_\sigma]\bigr\}.
--   $$
--
--   Let $\mathcal M$ be another finite-dimensional channel with its own fixed isometric dilation. Suppose $\mathcal N$ is antidegradable and $\mathcal M$ is entanglement breaking. For every $\lambda,\mu\ge0$,
--   $$
--   P_{\lambda,\mu}(\mathcal N\otimes\mathcal M)=P_{\lambda,\mu}(\mathcal N)+P_{\lambda,\mu}(\mathcal M).
--   $$
--   The product optimization permits arbitrary entangled joint inputs. The two single-channel maxima and their summed product maximum are attained. This is a factor-specific additivity statement.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 14, Corollary 4

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

/-- Corollary 4, PDF pp.14--15: the product maximum includes all entangled inputs.
The p.15 proof should retain XZ in the two final mutual informations. -/
theorem antidegradableEBAdditivity (V : Dilation I B E) (W : Dilation J D F)
    (hV : PhysicalDilation V) (hW : PhysicalDilation W) (hAnti : Antidegradable V)
    (hEB : ChannelEB (receiverChannel W))
    (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    AdditiveMax (values (dynamicObjective V lam mu)) (values (dynamicObjective W lam mu))
      (values (dynamicObjective (productDilation V W) lam mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
