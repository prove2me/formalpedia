-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_misclassification_variance_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.misclassification_variance_bound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:27:50.631727+00:00
-- url     : https://prove2.me/theorems/611d4b34-6456-44dd-ba4d-949f931e2cf3
-- title:
--   Appendix E Eq.(E6): one-sided variance bound
-- statement:
--   In the equal-prior setting of Lemma 2, let the measurable output $X$ have finite second moment under class-0 law $\mu_0$. Suppose class-1 outputs equal $c$, class-0 outputs lie in $[b_1,b_2]$, and $m=\mathbb E_0X>c$. Write $\delta=m-c>0$ and $v=\operatorname{Var}_0X$. Then
--
--   $$\Pr(0\mid X=c)\le\Pr(X=c\mid0)\le\Pr(m-X\ge\delta\mid0)\le\frac{v}{v+\delta^2}.$$
--
--   This is the one-sided variance bound with the tail direction corrected as forced by $m>c$. It concerns exact outputs and includes no unspecified additive measurement-noise model.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 27, Appendix E Eq.(E6): one-sided variance bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.27, Eq.(E6): the printed upper-tail sign is corrected to the lower
tail, forced by delta=mean-c>0. The variance and posterior bounds are retained.
No unspecified finite-shot noise model is introduced.
Printed: PDF p.27 E5-E6 uses X-mean >= delta while defining delta=mean-c>0.
Changed: Use mean-X >= delta in the entire displayed probability chain. Keep delta=mean-c>0, the atom X=c, equal priors, the constant class-1 output and the same variance/(variance+delta^2) bound.
Why: At X=c, mean-X=delta, whereas X-mean=-delta. Only the lower tail contains the atom being bounded. Cantelli has the same constant for either tail, so changing this one sign is the minimal repair. -/
theorem misclassification_variance_bound {Omega : Type*} [MeasurableSpace Omega]
    (mu0 mu1 : Measure Omega) [IsProbabilityMeasure mu0] [IsProbabilityMeasure mu1]
    (X : Omega → ℝ) (hX : Measurable X) (hL2 : MemLp X 2 mu0)
    (c b1 b2 : ℝ) (hclass1 : ∀ᵐ w ∂mu1, X w = c)
    (hclass0 : ∀ᵐ w ∂mu0, X w ∈ Set.Icc b1 b2)
    (hmean : c < ∫ w, X w ∂mu0) :
    let delta := (∫ w, X w ∂mu0) - c
    posteriorAt mu0 mu1 X c ≤ (mu0 {w | X w = c}).toReal ∧
    (mu0 {w | X w = c}).toReal ≤
      (mu0 {w | delta ≤ (∫ z, X z ∂mu0) - X w}).toReal ∧
    (mu0 {w | delta ≤ (∫ z, X z ∂mu0) - X w}).toReal ≤
      variance X mu0 / (variance X mu0 + delta ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
