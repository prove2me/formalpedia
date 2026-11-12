-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_nullAdmissibleDomination
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.nullAdmissibleDomination
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T06:11:36.867683+00:00
-- url     : https://prove2.me/theorems/fe0753b9-4e20-45c4-9f74-b11de006228b
-- title:
--   §5.2, null-admissible reduction
-- statement:
--   For finite laws $p,q$, $n\ge1$, and any nonrandomized test on the observable sample space $D_0^n\cup D_1^n$, there is a null-admissible test $g$, accepting $p$ on $D_0^n\setminus B^n$ and $q$ on $D_1^n\setminus B^n$, such that
--
--   $$\alpha_n(g)\le\alpha_n(f),\qquad\beta_n(g)\le\beta_n(f).$$
--
--   Here $D_0,D_1$ are the positive supports and $B=D_0\cap D_1$. Thus null admissibility loses no attainable error performance in this nonrandomized setting.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 22, §5.2, null-admissible reduction

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

/-- arXiv:0708.4282v1, PDF pp.22,23: §5.2, null-admissible reduction. -/
theorem nullAdmissibleDomination (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q) (n : ℕ) (hn : 0 < n)
    (f : ObservableWords p q n → Bool) :
    ∃ g : ObservableWords p q n → Bool, NullAdmissible p q g ∧
      observableAlpha p q g ≤ observableAlpha p q f ∧
      observableBeta p q g ≤ observableBeta p q f := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
