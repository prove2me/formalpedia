-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_strengthened_jensen
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.strengthened_jensen
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:45:50.442791+00:00
-- url     : https://prove2.me/theorems/250ed8e9-0a47-4d12-8ddf-a821286d970e
-- title:
--   Lemma 1: Strengthened Jensen: beta J(P0,K,f)<=J(P1,K,f), beta=ess inf_(P0) dP1/dP0, with J(Pi,K,f)=E f(E[Zi|Xi])-f(E Zi)
-- statement:
--   Let $P_1\ll P_0$ be probability measures, let $K:A\to\mathcal P(\mathbb R)$ be one common measurable Markov kernel, and let $f:\mathbb R\to\mathbb R$ be convex. Suppose the kernel output $Z_i$ is integrable under each joint law $P_iK$. With $m(x)=\int zK(x,dz)$ and $\beta=\operatorname*{ess\,inf}_{P_0}(dP_1/dP_0)$,
--
--   $$\beta\left(E_{P_0}f(m(X))-f(E_{P_0}m(X))\right)
--   \le E_{P_1}f(m(X))-f(E_{P_1}m(X)).$$
--
--   Outer expectations may be infinite; convexity supplies an affine lower bound and hence an integrable negative part. The conditional mean is computed from the kernel, not supplied as an unrelated variable.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 33, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Lemma 1: Strengthened Jensen: inverseUpperDensity J(P0,K,f)<=J(P1,K,f), inverseUpperDensity=ess inf_(P0) dP1/dP0, with J(Pi,K,f)=E f(E[Zi|Xi])-f(E Zi). Sason--Verdu, arXiv:1508.00335v7, PDF p.33.  -/
theorem strengthened_jensen
    (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P) (K : ProbabilityTheory.Kernel A ℝ) [ProbabilityTheory.IsMarkovKernel K]
    (hP : Integrable (fun z : A × ℝ => z.2) (P ⊗ₘ K))
    (hQ : Integrable (fun z : A × ℝ => z.2) (Q ⊗ₘ K)) :
    ((essInf (Q.rnDeriv P) P : ℝ≥0∞) : EReal) * jensenGap f P K ≤ jensenGap f Q K := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
