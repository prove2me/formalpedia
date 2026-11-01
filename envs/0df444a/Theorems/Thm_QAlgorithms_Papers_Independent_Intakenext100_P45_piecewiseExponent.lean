-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_piecewiseExponent
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.piecewiseExponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:14:18.050735+00:00
-- url     : https://prove2.me/theorems/fdb67aa2-5959-42aa-a308-ba6c62e7877e
-- title:
--   Lemma 4, piecewise exponent
-- statement:
--   For nonorthogonal finite laws $p,q$, with overlap masses $\psi_0,\psi_1>0$ and conditional exponent $\widetilde e$, the original exponent is
--
--   $$e(r)=\begin{cases}+\infty,&0\le r<-\log\psi_1,\\-\log\psi_0+\widetilde e(r+\log\psi_1),&r\ge-\log\psi_1.\end{cases}$$
--
--   The threshold belongs to the finite branch. This corrects the reversed inequality printed in Lemma 4 using its own proof.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 24, Lemma 4, piecewise exponent

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

/-- arXiv:0708.4282v1, PDF p.24: Lemma 4, piecewise exponent. Source correction: PDF p.24 finite branch prints r<=-log psi1; changed to r>=-log psi1, as the proof explicitly assumes and proves. Rendered PDF checked; independent moderation required. -/
theorem piecewiseExponent (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q)
    (h0 : 0 < overlapMass p q) (h1 : 0 < overlapMass q p) (r : ℝ) (hr : 0 ≤ r) :
    classicalExponent p q r =
      if r < -Real.log (overlapMass q p) then ⊤
      else (((-Real.log (overlapMass p q) : ℝ) : EReal)+
        conditionalExponent p q (r+Real.log (overlapMass q p))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
