-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_arbitraryClassicalHBCL
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.arbitraryClassicalHBCL
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:15:09.573705+00:00
-- url     : https://prove2.me/theorems/e5f8face-2e2d-4b16-9173-fba5199e41a4
-- title:
--   Theorem 4, classical HBCL for arbitrary laws
-- statement:
--   For arbitrary finite probability laws $p,q$, the full HBCL achievability and strict converse hold with the extended exponent defined by (42). In particular,
--
--   $$0\le r<-\log\psi_1\Longrightarrow e(r)=+\infty,$$
--
--   where $\psi_1=q(\operatorname{supp}p\cap\operatorname{supp}q)$ and $-\log0=+\infty$. Infinite exponents at $r>0$ are achievable with identically zero type-I error. Orthogonal laws require no conditional distribution on an empty overlap.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 24, Theorem 4, classical HBCL for arbitrary laws

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

/-- arXiv:0708.4282v1, PDF pp.24,25: Theorem 4, classical HBCL for arbitrary laws. -/
theorem arbitraryClassicalHBCL (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q) :
    ClassicalHBCL p q ∧
    (∀ r : ℝ, 0 ≤ r → (r : EReal) < -logNonnegativeExtended (overlapMass q p) →
      classicalExponent p q r=⊤) ∧
    (∀ r : ℝ, 0 < r → classicalExponent p q r=⊤ →
      ∃ f : ClassicalTestSequence I, ∃ b : EReal,
        (∀ k, alphaSeq p f k=0) ∧ HasRate (betaSeq q f) b ∧ (r : EReal) ≤ b) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
