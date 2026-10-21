-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_erasureFormulaAndOneShot
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.erasureFormulaAndOneShot
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:52:36.935841+00:00
-- url     : https://prove2.me/theorems/1f118458-bbd7-4e72-afeb-6c12112e826d
-- title:
--   The erasure formula and its complete one-shot consequence
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
--   For the qubit erasure channel $\mathcal N_\epsilon$ with orthogonal flag and $\epsilon\in[0,1]$,
--   $$
--   P_{\lambda,\mu}(\mathcal N_\epsilon)=\max_{0\le p\le1/2}\left\{(1-\epsilon)+\lambda(1-2\epsilon)H_2(p)+\mu[(1-\epsilon)-\epsilon H_2(p)]\right\}.
--   $$
--   Both maxima are attained. In addition, its literal one-use region consists exactly of the real triples for which one common $p\in[0,1/2]$ satisfies
--   $$
--   R+P\le1-\epsilon,\qquad P+S\le(1-2\epsilon)H_2(p),\qquad R+P+S\le1-\epsilon-\epsilon H_2(p).
--   $$
--   This retains the lemma's final one-shot-region consequence. For $\epsilon\ge1/2$ antidegradability makes the $p=0$ endpoint optimal.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 22, Lemma 8

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

/-- Lemma 8, PDF pp.22--23: both the attained formula maximum and the final
one-shot-region consequence are retained. Antidegradability repairs eps >= 1/2. -/
theorem erasureFormulaAndOneShot (eps lam mu : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    EqualMax (values (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu))
      (intervalValues (erasureObjective eps lam mu)) ∧
    oneUseRPSRegion (erasureDilation (A := Fin 2) eps) = erasureRegion eps := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
