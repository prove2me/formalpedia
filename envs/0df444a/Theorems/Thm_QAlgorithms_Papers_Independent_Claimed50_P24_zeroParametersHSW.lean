-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_zeroParametersHSW
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.zeroParametersHSW
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:35:31.396213+00:00
-- url     : https://prove2.me/theorems/ae51a78c-ee94-43e2-9d43-b88ea0c91e50
-- title:
--   Zero supporting parameters recover the one-use HSW formula
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   The following attained maxima are equal:
--   $$
--   \max_\sigma I(XY;B)_\sigma=\max_{\{p_X,\rho_x\}} I(X;B).
--   $$
--   The right-hand mutual information is evaluated after sending $\rho_x$ through $\mathcal N$. Both sides permit arbitrary normalized mixed conditional states. This identifies the $\lambda=\mu=0$ one-use formula with the HSW formula; it does not identify an arbitrary channel's unregularized formula with its operational classical capacity.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 10, Corollary 1

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

/-- Corollary 1, PDF pp.10--11: equality of one-use formulas, not an assertion that
unregularized HSW is the classical capacity of every channel. -/
theorem zeroParametersHSW (V : Dilation I B E) (hV : PhysicalDilation V) :
    EqualMax (values (infoXYB V)) (singleValues (infoXB V)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
