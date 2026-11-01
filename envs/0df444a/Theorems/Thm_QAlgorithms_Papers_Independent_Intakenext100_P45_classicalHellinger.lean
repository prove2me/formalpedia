-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_classicalHellinger
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.classicalHellinger
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:08:57.988773+00:00
-- url     : https://prove2.me/theorems/6a7b251e-68a3-4b51-95ba-69d3fcf81103
-- title:
--   §4.8, classical Hellinger identities (34)–(37)
-- statement:
--   Let $p,q$ be finite probability laws with identical support. Define $Q_s=\sum_i p_i^{1-s}q_i^s$, $p_s(i)=p_i^{1-s}q_i^s/Q_s$, and $L(s)=\log Q_s$. Then $p_s$ is a probability law and, for $s\in[0,1]$,
--
--   $$H(p_s\|p)=sL'(s)-L(s),\qquad H(p_s\|q)=-(1-s)L'(s)-L(s).$$
--
--   A parameter minimizes $Q_s$ exactly when these two relative entropies coincide. A minimizer exists and satisfies $H(p_s\|p)=H(p_s\|q)=\xi(p,q)$. It is unique when $p\ne q$; for equal laws every parameter minimizes. Logs concern the common positive support; ambient zero coordinates are allowed.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 19, §4.8, classical Hellinger identities (34)–(37)

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

/-- arXiv:0708.4282v1, PDF p.19: §4.8, classical Hellinger identities (34)–(37). Source correction: PDF p.19 claims unconditional uniqueness; uniqueness is restricted to p != q, since equal laws have every s as a minimizer. Independent moderation required. -/
theorem classicalHellinger (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q) (heq : SamePositiveSupport p q) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      IsLaw (hellingerArc p q s) ∧
      kl (hellingerArc p q s) p =
        ((s*logDerivative p q s-Real.log (classicalOverlap p q s) : ℝ) : EReal) ∧
      kl (hellingerArc p q s) q =
        ((-(1-s)*logDerivative p q s-Real.log (classicalOverlap p q s) : ℝ) : EReal) ∧
      ((∀ t ∈ Set.Icc (0 : ℝ) 1, classicalOverlap p q s ≤ classicalOverlap p q t) ↔
        kl (hellingerArc p q s) p = kl (hellingerArc p q s) q)) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, classicalOverlap p q s ≤ classicalOverlap p q t) ∧
      kl (hellingerArc p q s) p = classicalDistance p q ∧
      kl (hellingerArc p q s) q = classicalDistance p q) ∧
    (p ≠ q → ∃! s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
      kl (hellingerArc p q s) p = kl (hellingerArc p q s) q) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
