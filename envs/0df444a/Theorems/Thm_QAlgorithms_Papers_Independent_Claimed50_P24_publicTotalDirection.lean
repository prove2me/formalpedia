-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_publicTotalDirection
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.publicTotalDirection
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:37:06.011989+00:00
-- url     : https://prove2.me/theorems/913fc52b-a589-4464-8de9-0846a07b4ee2
-- title:
--   The total-rate supporting direction recovers pure-ensemble HSW
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   Allow general mixed conditional states on the left and normalized pure inputs $|\psi_x\rangle$ on the right. Then the attained maxima obey
--   $$
--   \max_\sigma\bigl[I(XY;B)_\sigma-I(Y;E|X)_\sigma\bigr]
--   =\max_{\{p_X,\psi_x\}}I(X;B).
--   $$
--   The right side uses the receiver output of $|\psi_x\rangle\langle\psi_x|$, with $\|\psi_x\|=1$. This identifies the $\mu\to\infty$ supporting direction without asserting a raw unscaled limit.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 11, Corollary 3

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

/-- Corollary 3, PDF p.11: the RHS is optimized over normalized pure single-label inputs. -/
theorem publicTotalDirection (V : Dilation I B E) (hV : PhysicalDilation V) :
    EqualMax (values (fun A => infoXYB V A - infoYEX V A))
      (pureSingleValues (infoXB V)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
