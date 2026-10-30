-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_entropy_correction_dominant
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.entropy_correction_dominant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:49:43.45325+00:00
-- url     : https://prove2.me/theorems/d6e14efe-1f0c-410f-ad5b-b898c314c03f
-- title:
--   Unnumbered entropy-correction-dominant expansion
-- statement:
--   Let $\rho_n,\sigma_n$ be faithful density matrices on nonzero finite-dimensional complex Hilbert spaces $H_n$, for positive integers $n$. Let $w_n>0$ be nondecreasing with $w_n\to\infty$. Assume Condition 1: on one common disc $|z|<r$, $r>0$, the functions $E_n(z)=\log\operatorname{Tr}(\rho_n^{1-z}\sigma_n^z)$ have holomorphic extensions, $E_n(x)/w_n$ has a finite limit for each real $|x|<r$, and $|E_n(z)|/w_n$ is uniformly bounded in $n,z$. Write $D_n=D(\rho_n\Vert\sigma_n)$ for relative entropy in nats, $V_n=V(\rho_n\Vert\sigma_n)$ for information variance, and $d=\lim_nD_n/w_n$, $v=\lim_nV_n/w_n$. For $0<\varepsilon<1$, let $\beta_n(\varepsilon)$ be the infimum of $\operatorname{Tr}(\sigma_nT)$ over all effects $0\le T\le I$ satisfying $\operatorname{Tr}(\rho_n(I-T))\le\varepsilon$. Let $\Phi^{-1}$ denote the standard-normal quantile and set $t_*=\sqrt v\,\Phi^{-1}(\varepsilon)$.
--
--   Set $\Delta_nD=D_n-w_nd$, a possibly signed correction, and assume $\sqrt{w_n}=o(\Delta_nD)$, with little-o interpreted using absolute values. Then
--   $$-\log\beta_n(\varepsilon)=w_nd+\Delta_nD+o(\Delta_nD).$$
--
--   This identifies the second-order contribution when the entropy correction dominates the fluctuation scale, without assuming the correction is positive.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 10, Unnumbered entropy-correction-dominant expansion

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

/-- Unnumbered entropy-dominant expansion, PDF p.10. Little-o uses norms, so a signed
entropy correction is allowed; this says exponent-D_n=o(Delta_n D). -/
theorem entropy_correction_dominant (S : TestingSequence) (w : ℕ → ℝ)
    (hfaithful : FaithfulPairs S) (hcondition : ConditionOne S w)
    (epsilon : ℝ) (hepsilon : 0 < epsilon ∧ epsilon < 1)
    (hdominant : Asymptotics.IsLittleO atTop (fun k => Real.sqrt (w k))
      (relativeEntropyCorrection S w)) :
    Asymptotics.IsLittleO atTop
      (fun k => optimalTestingExponentNats (S.rho k) (S.sigma k) epsilon -
        (w k * relativeEntropyRate S w + relativeEntropyCorrection S w k)) (relativeEntropyCorrection S w) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
