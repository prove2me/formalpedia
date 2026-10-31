-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_lipschitz_reverse_pinsker
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.lipschitz_reverse_pinsker
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:39:56.365092+00:00
-- url     : https://prove2.me/theorems/c476f2a8-32dc-4e2b-ab5b-324a7effd47a
-- title:
--   Theorem 27: Df<=L TV for a continuous convex f:[0,infinity)→R, f(1)=0, L-Lipschitz on [beta2,beta1^{-1}]
-- statement:
--   Let $P\ll Q$ with $0<\beta_1<1$ and $0\le\beta_2<1$. Let $f:[0,\infty)\to\mathbb R$ be continuous and convex, normalized by $f(1)=0$, and $L$-Lipschitz on $[\beta_2,\beta_1^{-1}]$, where $L\ge0$. Then
--
--   $$D_f(P\|Q)\le L|P-Q|.$$
--
--   Continuity at zero is an actual hypothesis of this result; values of the Lean extension on negative reals are irrelevant.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 49, Theorem 27

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 27: Df<=L TV for a continuous convex f:[0,infinity)→R, f(1)=0, L-Lipschitz on [beta2,beta1^{-1}]. Sason--Verdu, arXiv:1508.00335v7, PDF p.49.  -/
theorem lipschitz_reverse_pinsker
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ici 0) f) (hc : ContinuousOn f (Ici 0))
    (hf1 : f 1 = 0) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q)
    (hb1 : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1)
    (L : ℝ≥0) (hL : LipschitzOnWith L f (Icc (inverseUpperDensity Q P) (inverseUpperDensity P Q)⁻¹)) :
    fDiv f P Q ≤ ((L : ℝ≥0∞) * fullVariation P Q : ℝ≥0∞) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
