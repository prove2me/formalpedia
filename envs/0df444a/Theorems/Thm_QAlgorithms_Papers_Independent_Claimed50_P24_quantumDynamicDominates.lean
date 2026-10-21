-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_quantumDynamicDominates
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.quantumDynamicDominates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:39:28.228017+00:00
-- url     : https://prove2.me/theorems/834d5ddf-8107-4610-98d0-c38c774d87ec
-- title:
--   The quantum dynamic formula dominates for degradable channels
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
--   Assume that a CPTP degrading map $B\to E$ exists. Define
--   $$
--   D_{\lambda,\mu}(\mathcal N)=\max_{\{p_X,\phi_x^{AA'}\}}\{I(AX;B)+\lambda I(A\rangle BX)+\mu[I(X;B)+I(A\rangle BX)]\},
--   $$
--   where each $\phi_x^{AA'}$ is pure and $A$ purifies the input $A'$. Then
--   $$
--   P_{\lambda,\mu}(\mathcal N)\le D_{\lambda,\mu}(\mathcal N).
--   $$
--   Both optima are attained. The weak inequality preserves the source's statement without interpreting its explanatory prose as a strict inequality.
--
--   **Formalization Note** Purity expands $I(AX;B)$ as $H(A'|X)+H(B)-H(E|X)$; the reference entropy is retained.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 13, Lemma 4

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

/-- Lemma 4, PDF p.13: weak domination by the quantum dynamic formula on degradable channels.
I(AX;B) retains the reference entropy and is not replaced by I(XY;B). -/
theorem quantumDynamicDominates (V : Dilation I B E) (hV : PhysicalDilation V)
    (hDeg : Degradable V) (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    LeMax (values (dynamicObjective V lam mu))
      (singleValues (quantumDynamicObjective V lam mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
