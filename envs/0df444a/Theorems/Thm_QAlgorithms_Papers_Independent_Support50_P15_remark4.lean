-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_remark4
-- name    : QAlgorithms.Papers.Independent.Support50.P15.remark4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:37:56.312919+00:00
-- url     : https://prove2.me/theorems/513c9bfa-f84c-450e-85c4-0c502afe4b18
-- title:
--   remark4
-- statement:
--   Fix $d\ge2$ and let $N(d)>0$ be the maximum in Eq. (7). The finite restriction of $M(\Delta,d)$ is smooth in a neighborhood of zero, and
--
--   $$M(0,d)=M'(0,d)=0,\quad M''(0,d)=\frac1{N(d)},\quad M^{(3)}(0,d)=\frac1{N(d)^2}.$$
--
--   Consequently its cubic Taylor polynomial is $\Delta^2/(2N(d))+\Delta^3/(6N(d)^2)$, the cubic lower bound of Theorem 2. The bound $M(\Delta,d)\ge\Delta^2/(2N(d))$ holds for $0\le\Delta\le\log d$ with the largest possible quadratic coefficient; it fails arbitrarily close to zero on the negative side. For $-1<t<1$, put $s=(1+t)/2$ and $r=(1-t)/2$. The explicit states $\tau_d(s),\tau_d(r)$ satisfy
--
--   $$\Delta=t\log(d-1),\qquad M(\Delta,d)\le D(\tau_d(s)\|\tau_d(r))=D_2(s\|r)=t\log\frac{1+t}{1-t}.$$
--
--   Their cubic lower bound with $N=N(d)$ tends to $2t^2$ as $d\to\infty$. This quantifies local optimality and supplies an explicit comparison family; the approximate ten-percent illustration is not an additional uniform theorem.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 5, remark4

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Remark 4, PDF p.5: smoothness, cubic Taylor data, optimal quadratic coefficient,
negative-side failure, and the explicit comparison family. -/
theorem remark4 (d : ℕ) (hd : 2 ≤ d) :
    let f := fun x => (tightBound d x).toReal
    (∃ e > 0, e < Real.log d ∧ ContDiffOn ℝ ⊤ f (Set.Ioo (-e) e)) ∧
    f 0 = 0 ∧ deriv f 0 = 0 ∧ deriv (deriv f) 0 = 1 / maxVariance d ∧
    deriv (deriv (deriv f)) 0 = 1 / (maxVariance d) ^ 2 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) (Real.log d), (x ^ 2 / (2 * maxVariance d) : ℝ) ≤ tightBound d x) ∧
    (∀ c : ℝ, (∀ x ∈ Set.Icc (0 : ℝ) (Real.log d), (c * x ^ 2 : ℝ) ≤ tightBound d x) →
      c ≤ 1 / (2 * maxVariance d)) ∧
    (∀ e > 0, ∃ x ∈ Set.Ioo (-min e (Real.log d)) 0,
      tightBound d x < (x ^ 2 / (2 * maxVariance d) : ℝ)) ∧
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      difference (family d ((1 + t) / 2)) (family d ((1 - t) / 2)) = t * Real.log ((d : ℝ) - 1) ∧
      binaryRelative ((1 + t) / 2) ((1 - t) / 2) = (t * Real.log ((1 + t) / (1 - t)) : ℝ) ∧
      tightBound d (t * Real.log ((d : ℝ) - 1)) ≤ binaryRelative ((1 + t) / 2) ((1 - t) / 2) ∧
      ∃ ha : IsDensityMatrix (family d ((1 + t) / 2)),
      ∃ hb : IsDensityMatrix (family d ((1 - t) / 2)),
        stateRelativeNats ⟨family d ((1 + t) / 2), ha⟩ ⟨family d ((1 - t) / 2), hb⟩ =
          binaryRelative ((1 + t) / 2) ((1 - t) / 2)) ∧
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1, Tendsto
      (fun n : ℕ => cubicBound (maxVariance n) (t * Real.log ((n : ℝ) - 1)))
      atTop (nhds (2 * t ^ 2))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
