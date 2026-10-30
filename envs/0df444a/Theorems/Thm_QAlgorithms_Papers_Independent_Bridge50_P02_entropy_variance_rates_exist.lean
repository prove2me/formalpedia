-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_entropy_variance_rates_exist
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.entropy_variance_rates_exist
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:48:14.92216+00:00
-- url     : https://prove2.me/theorems/dbf1a73e-a6d4-4996-aeab-19e0bf74c4b5
-- title:
--   Unnumbered consequence of Condition 1: entropy and variance rates exist
-- statement:
--   Let $\rho_n,\sigma_n$ be faithful density matrices on nonzero finite-dimensional complex Hilbert spaces $H_n$, for positive integers $n$. Let $w_n>0$ be nondecreasing with $w_n\to\infty$. Assume Condition 1: on one common disc $|z|<r$, $r>0$, the functions $E_n(z)=\log\operatorname{Tr}(\rho_n^{1-z}\sigma_n^z)$ have holomorphic extensions, $E_n(x)/w_n$ has a finite limit for each real $|x|<r$, and $|E_n(z)|/w_n$ is uniformly bounded in $n,z$. Write $D_n=D(\rho_n\Vert\sigma_n)$ for relative entropy in nats, $V_n=V(\rho_n\Vert\sigma_n)$ for information variance, and $d=\lim_nD_n/w_n$, $v=\lim_nV_n/w_n$. For $0<\varepsilon<1$, let $\beta_n(\varepsilon)$ be the infimum of $\operatorname{Tr}(\sigma_nT)$ over all effects $0\le T\le I$ satisfying $\operatorname{Tr}(\rho_n(I-T))\le\varepsilon$. Let $\Phi^{-1}$ denote the standard-normal quantile and set $t_*=\sqrt v\,\Phi^{-1}(\varepsilon)$.
--
--   The two displayed rate limits exist. More explicitly, the normalized analytic extensions converge on the common disc to an analytic function $E$, and
--   $$\frac{E_n'(0)}{w_n}\longrightarrow E'(0)=-d,\qquad\frac{E_n''(0)}{w_n}\longrightarrow E''(0)=v.$$
--
--   The rates are constructed as the corresponding limits, rather than introduced as free numbers with their convergence assumed. This justifies Definition 1.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 9, Unnumbered consequence of Condition 1

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

/-- Consequence before Definition 1, PDF p.9: analytic limit and both constructed rates exist.
The normalized first derivative tends to minus the entropy rate. -/
theorem entropy_variance_rates_exist (S : TestingSequence) (w : ℕ → ℝ)
    (hfaithful : FaithfulPairs S) (hcondition : ConditionOne S w) :
    Tendsto (fun k => finitePairRelativeEntropyNats (S.rho k) (S.sigma k) / w k) atTop
      (nhds (relativeEntropyRate S w)) ∧
    Tendsto (fun k => pairInformationVarianceNats (S.rho k) (S.sigma k) / w k) atTop
      (nhds (varianceRate S w)) ∧
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℕ → ℂ → ℂ, ∃ E : ℂ → ℂ,
      (∀ k, AnalyticOnNhd ℂ (H k) (Metric.ball 0 r)) ∧
      (∀ k x, |x| < r → H k (x : ℂ) = (realPetzLogOverlap (S.rho k) (S.sigma k) (1-x) : ℂ)) ∧
      AnalyticOnNhd ℂ E (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        Tendsto (fun k => H k z / (w k : ℂ)) atTop (nhds (E z))) ∧
      Tendsto (fun k => deriv (H k) 0 / (w k : ℂ)) atTop (nhds (deriv E 0)) ∧
      Tendsto (fun k => deriv (deriv (H k)) 0 / (w k : ℂ)) atTop
        (nhds (deriv (deriv E) 0)) ∧
      deriv E 0 = (-relativeEntropyRate S w : ℂ) ∧
      deriv (deriv E) 0 = (varianceRate S w : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
