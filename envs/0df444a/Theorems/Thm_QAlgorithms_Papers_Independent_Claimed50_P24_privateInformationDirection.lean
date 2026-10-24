-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_privateInformationDirection
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.privateInformationDirection
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:36:29.456718+00:00
-- url     : https://prove2.me/theorems/aa9402ae-1bbd-4ba5-86fa-4f55921b295d
-- title:
--   The private-information supporting direction
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   The attained private-information maxima satisfy
--   $$
--   \max_\sigma\bigl[I(Y;B|X)_\sigma-I(Y;E|X)_\sigma\bigr]
--   =\max_{\{p_X,\rho_x\}}\bigl[I(X;B)-I(X;E)\bigr].
--   $$
--   Both right-hand outputs come from the same isometric dilation. This is the displayed formula equality associated with the $\lambda\to\infty$ supporting direction with $\mu$ fixed; it is not a finite limit of the unscaled dynamic formula.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 11, Corollary 2

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

/-- Corollary 2, PDF p.11: the displayed equality of private-information maxima.
No unscaled infinite limit of P_{lambda,mu} is asserted. -/
theorem privateInformationDirection (V : Dilation I B E) (hV : PhysicalDilation V) :
    EqualMax (values (fun A => infoYBX V A - infoYEX V A))
      (singleValues (fun A => infoXB V A - infoXE V A)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
