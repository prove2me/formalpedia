-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_theorem3_collectiveLower
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.theorem3_collectiveLower
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:42:02.506914+00:00
-- url     : https://prove2.me/theorems/6396aa09-51db-4d79-b75f-be634aeea755
-- title:
--   Theorem 3
-- statement:
--   Fix integers $k,d,n,M\ge1$, $N\ge0$, $B>0$, and $0<\epsilon\le B/6$. An estimator may select any collective POVM on $N$ copies after receiving the known observable family, and its outcomes include the final real estimates. The POVM is independent of the unknown density matrix. Suppose it estimates every family of $M$ Hermitian observables of locality at most $k$, participation at most $d$, and spectral norm at most $B$, simultaneously to error $\epsilon$, with success at least $3/4$ on every density matrix. There is a universal $c>0$, before all these choices, such that
--   $$N\ge c\,\frac{B^2}{\epsilon^2}\log\min(M,n).$$
--   This is a worst-case task lower bound, not a lower bound for each fixed family. The small-error regime keeps the proof's hard-state perturbations positive, and the proof's accuracy rescaling is absorbed in $c$.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 8, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Theorem 3, paper p.8, Eq.26: worst-case lower bound against arbitrary
collective POVMs. The proof's accuracy eps/3 is absorbed into a universal
constant, with 0<eps≤B/6 keeping the hard states positive. -/
theorem theorem3_collectiveLower :
    ∃ c : ℝ, 0 < c ∧ ∀ (k d n M N : ℕ), 1 ≤ k → 1 ≤ d → 1 ≤ n → 1 ≤ M →
      ∀ (eps B : ℝ), 0 < eps → 0 < B → eps ≤ B / 6 →
      ∀ A : CollectiveEstimator n M N, SolvesTomography k d B eps A →
        c * B ^ 2 / eps ^ 2 * Real.log (min M n : ℕ) ≤ (N : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
