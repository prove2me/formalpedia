-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_commonBoundaryEnsemble
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.commonBoundaryEnsemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:47:47.338215+00:00
-- url     : https://prove2.me/theorems/754c3e32-6fdd-4c1d-87b6-d2294eb17f8b
-- title:
--   One explicit four-weight ensemble suffices for all three channel families
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with fixed isometric dilation $U:A'\to B\otimes E$ and complement $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. Entropies are in bits, with $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   For $\nu\in[0,1/2]$, use binary labels $X,Y$ and the ensemble whose four probabilities are
--   $$
--   p_{XY}(0,0)=p_{XY}(1,1)=\nu/2,\qquad
--   p_{XY}(0,1)=p_{XY}(1,0)=(1-\nu)/2,
--   \qquad \rho_{xy}=|y\rangle\langle y|.
--   $$
--   For each qubit dephasing channel with probability $p\in[0,1]$, each universal $1\to N$ cloning channel with $N\ge1$, and each qubit erasure channel with $\epsilon\in[0,1]$, the complete one-use three-inequality union is unchanged when restricted to these ensembles. Moreover, for every fixed pair of nonnegative supporting weights, some such ensemble attains the unrestricted dynamic objective maximum:
--   $$
--   \mathcal C^{(1)}(\mathcal N)=\bigcup_{0\le\nu\le1/2}\mathcal C^{(1)}_{\sigma_\nu}(\mathcal N),\qquad
--   \max_\sigma P_{\lambda,\mu}(\mathcal N;\sigma)=P_{\lambda,\mu}(\mathcal N;\sigma_\nu)
--   \quad\text{for some }\nu\in[0,1/2].
--   $$
--   Here $P_{\lambda,\mu}(\mathcal N;\sigma)$ denotes the three-term information objective in equation (15), before maximizing. The optimizing $\nu$ may depend on the channel and weights; the assertion does not impose a common value across different channels. The same ensemble form characterizes their boundaries.
--
--   The objective used above is
--   $$
--   P_{\lambda,\mu}(\mathcal N;\sigma)=I(XY;B)_\sigma+\lambda[I(Y;B|X)_\sigma-I(Y;E|X)_\sigma]+\mu[I(XY;B)_\sigma-I(Y;E|X)_\sigma],\qquad\lambda,\mu\ge0.
--   $$
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 20, Section 9 and Appendix A, eq. (24)

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

/-- Section 9, PDF p.17, and Appendix A eq.(24), pp.20--23: the same explicit
four-weight ensemble suffices for the full one-shot union and attains every finite
nonnegative supporting direction for each of the three channel families. The parameter can differ between channels and directions. -/
theorem commonBoundaryEnsemble (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      oneUseRPSRegion (dephasingDilation p) = {r | ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
        r ∈ stateRegion (dephasingDilation p) (boundaryEnsemble nu)} ∧
      ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
      (boundaryEnsemble nu).Valid ∧ (boundaryEnsemble nu).Pure ∧
      IsGreatest (values (dynamicObjective (dephasingDilation p) lam mu))
        (dynamicObjective (dephasingDilation p) lam mu (boundaryEnsemble nu))) ∧
    (∀ N : ℕ, 0 < N →
      oneUseRPSRegion (cloningDilation N) = {r | ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
        r ∈ stateRegion (cloningDilation N) (boundaryEnsemble nu)} ∧
      ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
      (boundaryEnsemble nu).Valid ∧ (boundaryEnsemble nu).Pure ∧
      IsGreatest (values (dynamicObjective (cloningDilation N) lam mu))
        (dynamicObjective (cloningDilation N) lam mu (boundaryEnsemble nu))) ∧
    (∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      oneUseRPSRegion (erasureDilation (A := Fin 2) eps) = {r | ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
        r ∈ stateRegion (erasureDilation (A := Fin 2) eps) (boundaryEnsemble nu)} ∧
      ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
      (boundaryEnsemble nu).Valid ∧ (boundaryEnsemble nu).Pure ∧
      IsGreatest (values (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu))
        (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu (boundaryEnsemble nu))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
