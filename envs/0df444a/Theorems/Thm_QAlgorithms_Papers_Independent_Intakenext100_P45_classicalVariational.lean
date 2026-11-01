-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_classicalVariational
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.classicalVariational
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:10:22.875736+00:00
-- url     : https://prove2.me/theorems/beaf874b-71e0-4b39-a66b-2f0b9fdd3d24
-- title:
--   §5.1, variational identity and profile (41)–(42)
-- statement:
--   For finite equivalent probability laws $p,q$, define $e(r)=\sup_{0\le s<1}[-rs-\log\sum_i p_i^{1-s}q_i^s]/(1-s)$. For every $r\ge0$,
--
--   $$e(r)=\min_{x:\,H(x\|q)\le r}H(x\|p),$$
--
--   where $x$ ranges over probability laws. An optimizer exists: it is $p$ if $H(p\|q)\le r$; otherwise it lies on $H(x\|q)=r$ and $e(r)>0$. The finite-valued function $e$ is convex and non-increasing, with $e(0)=H(q\|p)$ and $e(H(p\|q))=0$. This identifies the variational error profile.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 21, §5.1, variational identity and profile (41)–(42)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF pp.20,21: §5.1, variational identity and profile (41)–(42). -/
theorem classicalVariational (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q) (heq : SamePositiveSupport p q) :
    (∀ r : ℝ, 0 ≤ r →
      classicalExponent p q r = sInf {v : EReal | ∃ x : I → ℝ,
        IsLaw x ∧ kl x q ≤ (r : EReal) ∧ v=kl x p} ∧
      ∃ x : I → ℝ, IsLaw x ∧ kl x q ≤ (r : EReal) ∧
        classicalExponent p q r=kl x p ∧
        ((kl p q ≤ (r : EReal) → x=p ∧ classicalExponent p q r=0) ∧
         ((r : EReal) < kl p q → kl x q=(r : EReal) ∧ 0 < classicalExponent p q r))) ∧
    classicalExponent p q 0=kl q p ∧ classicalExponent p q (kl p q).toReal=0 ∧
    AntitoneOn (classicalExponent p q) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (fun r => (classicalExponent p q r).toReal) ∧
    (∀ r : ℝ, 0 ≤ r → classicalExponent p q r ≠ ⊤ ∧ classicalExponent p q r ≠ ⊥) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
