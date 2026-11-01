-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_conditionalTestBijection
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.conditionalTestBijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:12:10.876579+00:00
-- url     : https://prove2.me/theorems/f873756a-b1ec-40b1-9ff9-44488876af17
-- title:
--   Lemma 3, conditional-test bijection
-- statement:
--   Let finite laws $p,q$ have nonempty common support $B$, with masses $\psi_0=p(B)>0$, $\psi_1=q(B)>0$, and conditional laws $\widetilde p,\widetilde q$. For $n\ge1$, restriction to $B^n$ bijects null-admissible nonrandomized tests on $D_0^n\cup D_1^n$ with tests on $B^n$. Corresponding errors satisfy
--
--   $$\alpha_n=\psi_0^n\widetilde\alpha_n,\qquad\beta_n=\psi_1^n\widetilde\beta_n.$$
--
--   Removing doubly unobservable coordinates is essential to the bijection.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 23, Lemma 3, conditional-test bijection

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

/-- arXiv:0708.4282v1, PDF pp.22,23: Lemma 3, conditional-test bijection. -/
theorem conditionalTestBijection (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q)
    (h0 : 0 < overlapMass p q) (h1 : 0 < overlapMass q p) (n : ℕ) (hn : 0 < n) :
    Function.Bijective (fun f : {f : ObservableWords p q n → Bool // NullAdmissible p q f} =>
      restrictTest p q f.1) ∧
    (∀ f : ObservableWords p q n → Bool, NullAdmissible p q f →
      observableAlpha p q f = (overlapMass p q)^n * restrictedAlpha p q f ∧
      observableBeta p q f = (overlapMass q p)^n * restrictedBeta p q f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
