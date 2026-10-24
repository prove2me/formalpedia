-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_theorem2
-- name    : QAlgorithms.Papers.Independent.Support50.P15.theorem2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:36:21.336599+00:00
-- url     : https://prove2.me/theorems/ddd06215-965a-416e-aadf-ccdb8b6b36a3
-- title:
--   Properties of the sharp entropy-difference bound
-- statement:
--   For finite $d\ge2$, let $M(\Delta,d)$ be the constrained binary-relative-entropy minimum of Eq. (6), $N(d)=\max_{0<r<1/2}r(1-r)[\log(((1-r)/r)(d-1))]^2$ and $N_d=\tfrac14\log^2(d-1)+1$. The function $M$ is nonnegative, continuous in the extended order topology and strictly convex on $[-\log d,\log d]$, and its finite restriction is continuously differentiable in the interior. Its endpoint values are
--
--   $$M(0,d)=0,\quad M(-\log d,d)=\log d,\quad M(\log d,d)=+\infty.$$
--
--   It is finite on $[-\log d,\log d)$. One has $0<N(d)<N_d$ and $N(d)<\log^2 d$. For every real $N\ge N(d)$ and every real $\Delta$, using the empty-feasible-set extension of $M$,
--
--   $$M(\Delta,d)\ge N(e^{\Delta/N}-1-\Delta/N)\ge\frac{\Delta^2}{2N}+\frac{\Delta^3}{6N^2}.$$
--
--   On the entropy interval one also has $M(\Delta,d)\ge\Delta^2/(3\log^2 d)$. These provide explicit lower bounds without optimizing the scalar pair.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 4, theorem2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Theorem 2, PDF p.4; empty-feasible-set extension of (11) on p.21.
Continuity is extended-real continuity; differentiability uses only the finite interior. -/
theorem theorem2 (d : ℕ) (hd : 2 ≤ d) :
    (∀ delta ∈ Set.Icc (-Real.log d) (Real.log d), 0 ≤ tightBound d delta) ∧
    ContinuousOn (tightBound d) (Set.Icc (-Real.log d) (Real.log d)) ∧
    (∀ x ∈ Set.Icc (-Real.log d) (Real.log d),
      ∀ y ∈ Set.Icc (-Real.log d) (Real.log d), x ≠ y →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        tightBound d ((1 - t) * x + t * y) <
          ((1 - t : ℝ) : EReal) * tightBound d x + (t : EReal) * tightBound d y) ∧
    ContDiffOn ℝ 1 (fun x => (tightBound d x).toReal) (Set.Ioo (-Real.log d) (Real.log d)) ∧
    tightBound d 0 = 0 ∧ tightBound d (-Real.log d) = (Real.log d : ℝ) ∧
    tightBound d (Real.log d) = ⊤ ∧
    (∀ delta ∈ Set.Ico (-Real.log d) (Real.log d), tightBound d delta < ⊤) ∧
    0 < maxVariance d ∧ maxVariance d < easyVariance d ∧ maxVariance d < (Real.log d) ^ 2 ∧
    (∀ n : ℝ, maxVariance d ≤ n → ∀ delta : ℝ,
      (exponentialBound n delta : EReal) ≤ tightBound d delta ∧
      cubicBound n delta ≤ exponentialBound n delta) ∧
    (∀ delta ∈ Set.Icc (-Real.log d) (Real.log d),
      (delta ^ 2 / (3 * (Real.log d) ^ 2) : ℝ) ≤ tightBound d delta) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
