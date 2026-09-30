-- Prove2me | Theorems.Thm_UnderstandingML_hard_svm_generalization
-- name    : UnderstandingML.hard_svm_generalization
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:38:21.824309+00:00
-- url     : https://prove2.me/theorems/abcd8458-1594-4083-a2c4-04d8079da858
-- title:
--   Theorem 15.4: under (γ, ρ)-separability with a homogenous halfspace, w.p. ≥ 1 − δ the 0–1 error of the Hard-SVM output is at most √(4(ρ/γ)²/m) + √(2 log(2/δ)/m)
-- statement:
--   **Theorem 15.4.** Let $D$ be a distribution over $\mathbb{R}^d \times \{\pm1\}$ that satisfies the $(\gamma, \rho)$-separability with margin assumption using a homogenous halfspace. Then, with probability of at least $1 - \delta$ over the choice of a training set of size $m$, the 0–1 error of the output of Hard-SVM is at most
--   $$\sqrt{\frac{4(\rho/\gamma)^2}{m}} + \sqrt{\frac{2\log(2/\delta)}{m}}.$$
--
--   Formally: for a learner returning the homogenous Hard-SVM solution whenever the sample admits one, labels in $\{\pm1\}$ almost surely, $\gamma > 0$, $\delta \in (0,1)$ and $m \ge 1$; the failure event is bounded in outer measure.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.1.2 p. 206, Theorem 15.4 (= Theorem 26.13, proved in §26.3)

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 15.4** (p. 206) (= Theorem 26.13). Let `D` be a distribution over `ℝ^d × {±1}`
that satisfies the `(γ, ρ)`-separability with margin assumption using a homogenous halfspace.
Then with probability of at least `1 − δ` over the choice of a training set of size `m`, the 0–1
error of the output of Hard-SVM is at most `√(4(ρ/γ)²/m) + √(2 log(2/δ)/m)`. The learner `A`
returns a homogenous Hard-SVM solution whenever the sample admits one (it is unique). -/
theorem hard_svm_generalization {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    {γ ρ : ℝ} (hγ : 0 < γ) (hsep : HomSeparableWithMargin D γ ρ)
    (hlab : ∀ᵐ z ∂D, z.2 = 1 ∨ z.2 = -1) (A : Learner (Vec d × ℝ) (Vec d))
    (hA : ∀ (m : ℕ) (S : Fin m → Vec d × ℝ), (∃ w : Vec d, ∀ i, 1 ≤ (S i).2 * ⟪w, (S i).1⟫_ℝ) →
      IsHomHardSVM (fun i ↦ (S i).1) (fun i ↦ (S i).2) (A m S))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 0 < m) :
    iidLaw D m {S | Real.sqrt (4 * (ρ / γ) ^ 2 / m) + Real.sqrt (2 * Real.log (2 / δ) / m) <
        risk zeroOneLoss D (A m S)} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
