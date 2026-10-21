-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_classicalQuantumLePublicPrivate
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.classicalQuantumLePublicPrivate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:37:48.36698+00:00
-- url     : https://prove2.me/theorems/5de39e3c-c9b9-4cae-a7a7-046faa73fcd1
-- title:
--   The classical-quantum trade-off is bounded by the public-private trade-off
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   For $\mu\ge0$, define the distinct two-resource optima
--   $$
--   f_\mu(\mathcal N)=\max_{\{p_X,\rho_x\}}\{I(X;B)+(1+\mu)[H(B|X)-H(E|X)]\},\qquad
--   P_\mu(\mathcal N)=\max_\sigma\{I(X;B)+(1+\mu)[I(Y;B|X)-I(Y;E|X)]\}.
--   $$
--   For $f_\mu$, a reference $A$ purifies each conditional input, so $I(A\rangle BX)=H(B|X)-H(E|X)$. This entropy representation ranges over all purified inputs, without a restriction on their purifying reference.
--
--   Then
--   $$
--   f_\mu(\mathcal N)\le P_\mu(\mathcal N).
--   $$
--   Both maxima are attained. This compares communication without entanglement or key assistance in the two resource settings.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 11, Lemma 2

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

/-- Lemma 2, PDF pp.11--12: the classical-quantum trade-off never exceeds the distinct
public-private trade-off, for mu >= 0. Purifying references are eliminated by entropy identities. -/
theorem classicalQuantumLePublicPrivate (V : Dilation I B E) (hV : PhysicalDilation V)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    LeMax (singleValues (classicalQuantumObjective V mu))
      (values (publicPrivateObjective V mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
