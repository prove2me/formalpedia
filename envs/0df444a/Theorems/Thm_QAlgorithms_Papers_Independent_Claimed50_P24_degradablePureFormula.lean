-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_degradablePureFormula
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.degradablePureFormula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:44:10.535838+00:00
-- url     : https://prove2.me/theorems/5dfa3c18-e46c-4791-af18-d5a4abdb28e7
-- title:
--   Pure conditional inputs suffice for the degradable formula
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
--   Suppose $\mathcal N$ is degradable, and let $\omega$ range over the same ensemble construction with every conditional input pure and normalized. Define
--   $$
--   g_{\lambda,\mu}(\mathcal N)=\max_\omega\{I(XY;B)_\omega+\lambda[H(B|X)_\omega-H(E|X)_\omega]+\mu[H(B)_\omega-H(E|X)_\omega]\}.
--   $$
--   Then, with both maxima attained,
--   $$
--   P_{\lambda,\mu}(\mathcal N)=g_{\lambda,\mu}(\mathcal N).
--   $$
--   The original optimum still ranges over mixed conditional inputs. The conclusion authorizes the pure-state simplification only for the degradable channel class.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 15, Lemma 6

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

/-- Lemma 6, PDF pp.15--16: general mixed inputs remain on the LHS, and pure conditional
inputs suffice only on the simplified RHS. No false spectral-refinement equality is assumed. -/
theorem degradablePureFormula (V : Dilation I B E) (hV : PhysicalDilation V)
    (hDeg : Degradable V) (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    EqualMax (values (dynamicObjective V lam mu))
      (pureValues (pureDynamicObjective V lam mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
