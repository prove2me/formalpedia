-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_conditionalHBCL
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.conditionalHBCL
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:13:41.83968+00:00
-- url     : https://prove2.me/theorems/c20c2d72-6a13-4535-8b77-d37ef0cc4063
-- title:
--   Proposition 3, unequal-support conditional HBCL
-- statement:
--   For nonorthogonal finite laws put $a=-\log\psi_1$, $b=-\log\psi_0$, and let $\widetilde e$ be the conditional Hoeffding exponent. For each $r\ge a$, some test sequence has existing rates
--
--   $$\beta_R\ge r,\qquad\alpha_R=b+\widetilde e(r-a).$$
--
--   For $0\le r\le a$, some test sequence has $\alpha_n=0$ and $-n^{-1}\log\beta_n=a$ for every positive $n$. Conversely, if both rates exist and $\beta_R>r\ge a$, then $\alpha_R\le b+\widetilde e(r-a)$. Orthogonal laws are handled separately by the arbitrary-law theorem.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 23, Proposition 3, unequal-support conditional HBCL

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

/-- arXiv:0708.4282v1, PDF pp.23,24: Proposition 3, unequal-support conditional HBCL. -/
theorem conditionalHBCL (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q)
    (h0 : 0 < overlapMass p q) (h1 : 0 < overlapMass q p) :
    (∀ r : ℝ, -Real.log (overlapMass q p) ≤ r →
      ∃ f : ClassicalTestSequence I, ∃ b : EReal,
        HasRate (alphaSeq p f)
          (((-Real.log (overlapMass p q) : ℝ) : EReal)+conditionalExponent p q (r+Real.log (overlapMass q p))) ∧
        HasRate (betaSeq q f) b ∧ (r : EReal) ≤ b) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ -Real.log (overlapMass q p) →
      ∃ f : ClassicalTestSequence I, ∀ k,
        rateTerm (betaSeq q f k) k=((-Real.log (overlapMass q p) : ℝ) : EReal) ∧ alphaSeq p f k=0) ∧
    (∀ (f : ClassicalTestSequence I) (a b : EReal) (r : ℝ),
      -Real.log (overlapMass q p) ≤ r → HasRate (alphaSeq p f) a → HasRate (betaSeq q f) b →
      (r : EReal) < b → a ≤
        (((-Real.log (overlapMass p q) : ℝ) : EReal)+conditionalExponent p q (r+Real.log (overlapMass q p)))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
