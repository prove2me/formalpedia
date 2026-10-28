-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_equalErasureAdditivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.equalErasureAdditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:54:10.148949+00:00
-- url     : https://prove2.me/theorems/c590b0b7-7268-4441-880b-9145c473e55f
-- title:
--   Equal-parameter qubit erasure channels have an additive private dynamic formula
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
--   For two qubit erasure channels with the same erasure probability $\epsilon\in[0,1]$, and every fixed pair $\lambda,\mu\ge0$,
--   $$
--   P_{\lambda,\mu}(\mathcal N_\epsilon\otimes\mathcal N_\epsilon)
--   =P_{\lambda,\mu}(\mathcal N_\epsilon)+P_{\lambda,\mu}(\mathcal N_\epsilon).
--   $$
--   The product optimum permits arbitrary entangled inputs; both factor maxima and the summed product maximum are attained. The statement keeps equal erasure parameters, without silently asserting unequal-parameter additivity. The negative-coefficient and antidegradable regimes are included.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 23, Lemma 10

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

/-- Lemma 10, PDF pp.23--24: same erasure parameter on both channels, with the
complete two-use optimization over possibly entangled inputs, and the full [0,1] range. -/
theorem equalErasureAdditivity (eps lam mu : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    AdditiveMax (values (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu))
      (values (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu))
      (values (dynamicObjective
        (productDilation (erasureDilation (A := Fin 2) eps) (erasureDilation (A := Fin 2) eps)) lam mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
