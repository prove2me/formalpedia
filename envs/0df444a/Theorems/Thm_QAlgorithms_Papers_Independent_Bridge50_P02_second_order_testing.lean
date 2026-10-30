-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_second_order_testing
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.second_order_testing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:39:17.280252+00:00
-- url     : https://prove2.me/theorems/6ce36ce3-06c7-4566-8ba7-9fc7294b33b5
-- title:
--   Theorem 1: second-order testing bounds beyond IID (seed result)
-- statement:
--   Let $\rho_n,\sigma_n$ be faithful density matrices on nonzero finite-dimensional complex Hilbert spaces $H_n$, for positive integers $n$. Let $w_n>0$ be nondecreasing with $w_n\to\infty$. Assume Condition 1: on one common disc $|z|<r$, $r>0$, the functions $E_n(z)=\log\operatorname{Tr}(\rho_n^{1-z}\sigma_n^z)$ have holomorphic extensions, $E_n(x)/w_n$ has a finite limit for each real $|x|<r$, and $|E_n(z)|/w_n$ is uniformly bounded in $n,z$. Write $D_n=D(\rho_n\Vert\sigma_n)$ for relative entropy in nats, $V_n=V(\rho_n\Vert\sigma_n)$ for information variance, and $d=\lim_nD_n/w_n$, $v=\lim_nV_n/w_n$. For $0<\varepsilon<1$, let $\beta_n(\varepsilon)$ be the infimum of $\operatorname{Tr}(\sigma_nT)$ over all effects $0\le T\le I$ satisfying $\operatorname{Tr}(\rho_n(I-T))\le\varepsilon$. Let $\Phi^{-1}$ denote the standard-normal quantile and set $t_*=\sqrt v\,\Phi^{-1}(\varepsilon)$.
--
--   For every $t>t_*$ there is a real function $f_t=o(\sqrt{x})$ as $x\to+\infty$ such that, for every $n\ge1$,
--   $$-\log\beta_n(\varepsilon)\le D_n+\sqrt{w_n}\,t+f_t(w_n).$$
--   For every $t<t_*$ and every real $f=o(\sqrt{x})$, the reverse inequality
--   $$-\log\beta_n(\varepsilon)\ge D_n+\sqrt{w_n}\,t+f(w_n)$$
--   holds for all sufficiently large $n$. The statement permits $v=0$ and repeated weights.
--
--   These bounds identify the second-order testing scale without an IID hypothesis.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 9, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Theorem 1, PDF pp.9--10, (3.3)--(3.4). No strict positivity of the variance rate. -/
theorem second_order_testing (S : TestingSequence) (w : ℕ → ℝ)
    (hfaithful : FaithfulPairs S) (hcondition : ConditionOne S w)
    (epsilon : ℝ) (hepsilon : 0 < epsilon ∧ epsilon < 1) :
    SecondOrderBounds S w (fun k => finitePairRelativeEntropyNats (S.rho k) (S.sigma k)) epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
