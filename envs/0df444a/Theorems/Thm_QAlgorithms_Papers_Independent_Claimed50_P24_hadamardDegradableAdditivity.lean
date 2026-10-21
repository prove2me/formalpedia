-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_hadamardDegradableAdditivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.hadamardDegradableAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:44:50.056727+00:00
-- url     : https://prove2.me/theorems/e74e8d57-a6e4-4750-8c23-264f660689ef
-- title:
--   Hadamard and degradable channels have an additive private dynamic formula
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
--   Let $\mathcal H$ and $\mathcal D$ be finite-dimensional channels with fixed dilations. Assume $\mathcal H^c$ is entanglement breaking, so $\mathcal H$ is a quantum Hadamard channel, and assume $\mathcal D$ has a CPTP degrading map from its receiver to its complement. Then
--   $$
--   P_{\lambda,\mu}(\mathcal H\otimes\mathcal D)=P_{\lambda,\mu}(\mathcal H)+P_{\lambda,\mu}(\mathcal D),\qquad \lambda,\mu\ge0.
--   $$
--   All three maxima are attained, and the product input may be entangled. The Hadamard-channel property supplies the measurement/preparation structure used in the source argument; it is unrelated to the Hadamard gate.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 16, Lemma 7

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

/-- Lemma 7, PDF pp.16--17: a Hadamard channel and a degradable channel have additive
private dynamic formulas. Hadamard is the channel property, not the one-qubit gate. -/
theorem hadamardDegradableAdditivity (V : Dilation I B E) (W : Dilation J D F)
    (hV : PhysicalDilation V) (hW : PhysicalDilation W) (hHad : Hadamard V) (hDeg : Degradable W)
    (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    AdditiveMax (values (dynamicObjective V lam mu)) (values (dynamicObjective W lam mu))
      (values (dynamicObjective (productDilation V W) lam mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
