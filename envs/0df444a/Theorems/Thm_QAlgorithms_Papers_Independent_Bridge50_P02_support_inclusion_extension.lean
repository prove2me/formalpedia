-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_support_inclusion_extension
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.support_inclusion_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:49:01.526719+00:00
-- url     : https://prove2.me/theorems/a61bf3ba-064d-4f8f-8dcc-894cf2c2a7d0
-- title:
--   Remark 1: support-inclusion extension of the main asymptotic results
-- statement:
--   Let $\rho_n,\sigma_n$ be density matrices satisfying $\operatorname{supp}\rho_n\subseteq\operatorname{supp}\sigma_n$ on nonzero finite-dimensional complex Hilbert spaces $H_n$, for positive integers $n$. Let $w_n>0$ be nondecreasing with $w_n\to\infty$. Assume Condition 1: on one common disc $|z|<r$, $r>0$, the functions $E_n(z)=\log\operatorname{Tr}(\rho_n^{1-z}\sigma_n^z)$ have holomorphic extensions, $E_n(x)/w_n$ has a finite limit for each real $|x|<r$, and $|E_n(z)|/w_n$ is uniformly bounded in $n,z$. Write $D_n=D(\rho_n\Vert\sigma_n)$ for relative entropy in nats, $V_n=V(\rho_n\Vert\sigma_n)$ for information variance, and $d=\lim_nD_n/w_n$, $v=\lim_nV_n/w_n$. For $0<\varepsilon<1$, let $\beta_n(\varepsilon)$ be the infimum of $\operatorname{Tr}(\sigma_nT)$ over all effects $0\le T\le I$ satisfying $\operatorname{Tr}(\rho_n(I-T))\le\varepsilon$. Let $\Phi^{-1}$ denote the standard-normal quantile and set $t_*=\sqrt v\,\Phi^{-1}(\varepsilon)$.
--
--   The entropy and variance rate limits exist, and the two testing bounds of Theorem 1 hold:
--   For every $t>t_*$ there is a real function $f_t=o(\sqrt{x})$ as $x\to+\infty$ such that, for every $n\ge1$,
--   $$-\log\beta_n(\varepsilon)\le D_n+\sqrt{w_n}\,t+f_t(w_n).$$
--   For every $t<t_*$ and every real $f=o(\sqrt{x})$, the reverse inequality
--   $$-\log\beta_n(\varepsilon)\ge D_n+\sqrt{w_n}\,t+f(w_n)$$
--   holds for all sufficiently large $n$. The statement permits $v=0$ and repeated weights.
--   If $D_n-w_nd=o(\sqrt{w_n})$, both bounds also hold with center $w_nd$. If $\sqrt{w_n}=o(D_n-w_nd)$, then $-\log\beta_n(\varepsilon)-D_n=o(D_n-w_nd)$.
--
--   This is the support-inclusion extension of the main asymptotic statements. Spectral powers are support restricted, and the spaces remain finite dimensional.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 9, Remark 1

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

/-- Remark 1, PDF p.9: finite-dimensional support-inclusion extension of the main
asymptotic conclusions. Spectral powers vanish at zero and no singular modular inverse is used. -/
theorem support_inclusion_extension (S : TestingSequence) (w : ℕ → ℝ)
    (hcondition : ConditionOne S w) (epsilon : ℝ) (hepsilon : 0 < epsilon ∧ epsilon < 1) :
    Tendsto (fun k => finitePairRelativeEntropyNats (S.rho k) (S.sigma k) / w k) atTop
      (nhds (relativeEntropyRate S w)) ∧
    Tendsto (fun k => pairInformationVarianceNats (S.rho k) (S.sigma k) / w k) atTop
      (nhds (varianceRate S w)) ∧
    SecondOrderBounds S w (fun k => finitePairRelativeEntropyNats (S.rho k) (S.sigma k)) epsilon ∧
    (Asymptotics.IsLittleO atTop (relativeEntropyCorrection S w) (fun k => Real.sqrt (w k)) →
      SecondOrderBounds S w (fun k => w k * relativeEntropyRate S w) epsilon) ∧
    (Asymptotics.IsLittleO atTop (fun k => Real.sqrt (w k)) (relativeEntropyCorrection S w) →
      Asymptotics.IsLittleO atTop
        (fun k => optimalTestingExponentNats (S.rho k) (S.sigma k) epsilon -
          (w k * relativeEntropyRate S w + relativeEntropyCorrection S w k)) (relativeEntropyCorrection S w)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
