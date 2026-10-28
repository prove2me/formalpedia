-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_erasureRedundantDirections
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.erasureRedundantDirections
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:53:32.139262+00:00
-- url     : https://prove2.me/theorems/e297f9eb-bc90-46d5-9ba7-6e62f19107f9
-- title:
--   Negative erasure entropy coefficient selects the public endpoint and a redundant direction
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with fixed isometric dilation $U:A'\to B\otimes E$ and complement $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. Entropies are in bits, with $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   For fixed $\lambda,\mu\ge0$, define the attained one-use optimum
--   $$
--   P_{\lambda,\mu}(\mathcal N)=\max_\sigma\bigl\{I(XY;B)_\sigma+\lambda[I(Y;B|X)_\sigma-I(Y;E|X)_\sigma]+\mu[I(XY;B)_\sigma-I(Y;E|X)_\sigma]\bigr\}.
--   $$
--
--   Let $\epsilon\in[0,1]$ and $\lambda,\mu\ge0$. Suppose
--   $$
--   \lambda(1-2\epsilon)<\mu\epsilon.
--   $$
--   Then the erasure expression is maximized at $p=0$, and
--   $$
--   P_{\lambda,\mu}(\mathcal N_\epsilon)=(1+\mu)(1-\epsilon).
--   $$
--   The one-state region of the common four-weight ensemble at $p=0$ is exactly $(1-\epsilon,0,0)+\mathcal U$, where $\mathcal U$ is the unit conversion cone. Every triple satisfying $R+P\le1-\epsilon$, $P+S\le0$, and $R+P+S\le1-\epsilon$ satisfies
--   $$
--   R+P+\lambda(P+S)+\mu(R+P+S)\le(1+\mu)(1-\epsilon).
--   $$
--   Hence this negative-coefficient supporting direction adds no restriction beyond the translated public-endpoint cone. Only directions with $\lambda(1-2\epsilon)\ge\mu\epsilon$ can contribute a nontrivial erasure trade-off; this is not a global restriction on allowed weights or channel probabilities.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 23, Lemma 9

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

/-- Lemma 9, PDF p.23: a strictly negative entropy coefficient selects the public
endpoint, and its supporting inequality is redundant on that endpoint's translated
unit cone. This is not a restriction on channel probabilities or on all multipliers. -/
theorem erasureRedundantDirections (eps lam mu : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hneg : lam * (1 - 2 * eps) < mu * eps) :
    IsGreatest (values (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu))
      ((1 + mu) * (1 - eps)) ∧
    IsGreatest (intervalValues (erasureObjective eps lam mu))
      (erasureObjective eps lam mu 0) ∧
    stateRegion (erasureDilation (A := Fin 2) eps) (boundaryEnsemble 0) =
      {r | ∃ u ∈ unitCone, r = (![1 - eps, 0, 0] : Rate) + u} ∧
    (∀ r : Rate, r 0 + r 1 ≤ 1 - eps → r 1 + r 2 ≤ 0 →
      r 0 + r 1 + r 2 ≤ 1 - eps → rpsSupport lam mu r ≤ (1 + mu) * (1 - eps)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
