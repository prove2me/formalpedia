-- Prove2me | Theorems.Thm_UnderstandingML_hard_svm_generalization_rademacher
-- name    : UnderstandingML.hard_svm_generalization_rademacher
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:44:41.63141+00:00
-- url     : https://prove2.me/theorems/9945d252-e2c6-4500-a1b0-61a353837a9b
-- title:
--   Theorem 26.13: for separable-with-margin data with ‖x‖ ≤ R, the hard-SVM output has P[y⟨w_S,x⟩ ≤ 0] ≤ 2R‖w⋆‖/√m + (1 + R‖w⋆‖)√(2ln(2/δ)/m) w.p. ≥ 1−δ
-- statement:
--   **Theorem 26.13.** Consider a distribution $D$ over $X \times \{\pm1\}$ such that there exists some vector $w^\star$ with $P_{(x,y) \sim D}[y\langle w^\star, x\rangle \ge 1] = 1$ and such that $\|x\|_2 \le R$ with probability $1$. Let $w_S$ be the output of Equation (26.19), $\operatorname{argmin}_w\|w\|^2$ s.t. $\forall i, y_i\langle w, x_i\rangle \ge 1$. Then, with probability of at least $1 - \delta$ over the choice of $S \sim D^m$, we have that
--   $$P_{(x,y) \sim D}[y \ne \operatorname{sign}(\langle w_S, x\rangle)] \le \frac{2R\|w^\star\|}{\sqrt m} + (1 + R\|w^\star\|)\sqrt{\frac{2\ln(2/\delta)}{m}}.$$
--
--   Formally: real labels $\pm1$ almost surely; the error is $P[y\langle w_S, x\rangle \le 0]$, which dominates $P[y \ne \operatorname{sign}\langle w_S, x\rangle]$ for every convention for $\operatorname{sign}(0)$; the learner returns a hard-SVM solution on every sample separable with margin $1$; $X$ a separable Hilbert space, $m \ge 1$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.3 pp. 384-385, Theorem 26.13 with its proof (via the ramp loss and Theorem 26.12)

import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 26.13** (p. 384). Consider a distribution `D` over `X × {±1}` such that there
exists some vector `w⋆` with `P_{(x,y) ∼ D}[y⟨w⋆, x⟩ ≥ 1] = 1` and such that `‖x‖₂ ≤ R` with
probability `1`. Let `w_S` be the output of hard-SVM (26.19), `argmin ‖w‖²` s.t. `yᵢ⟨w, xᵢ⟩ ≥ 1`.
Then, with probability of at least `1 − δ` over the choice of `S ∼ D^m`,
`P_{(x,y) ∼ D}[y ≠ sign(⟨w_S, x⟩)] ≤ 2R‖w⋆‖/√m + (1 + R‖w⋆‖) √(2 ln(2/δ)/m)`.
Labels are real `±1`; the error is stated as `P[y⟨w_S, x⟩ ≤ 0]`, which bounds `P[y ≠ sign(⟨w_S, x⟩)]`
for every convention for `sign(0)`; the learner returns a hard-SVM solution on every separable
sample. `X` is a separable Hilbert space, `m ≥ 1`. -/
theorem hard_svm_generalization_rademacher {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (D : Measure (E × ℝ)) [IsProbabilityMeasure D] (hy : D {p | p.2 ≠ 1 ∧ p.2 ≠ -1} = 0)
    (wstar : E) (hsep : D {p | p.2 * ⟪wstar, p.1⟫_ℝ < 1} = 0) (R : ℝ) (hR : D {p | R < ‖p.1‖} = 0)
    (A : Learner (E × ℝ) E)
    (hA : ∀ (m : ℕ) (S : Fin m → E × ℝ), (∃ w : E, ∀ i, 1 ≤ (S i).2 * ⟪w, (S i).1⟫_ℝ) →
      (∀ i, 1 ≤ (S i).2 * ⟪A m S, (S i).1⟫_ℝ) ∧
      ∀ w' : E, (∀ i, 1 ≤ (S i).2 * ⟪w', (S i).1⟫_ℝ) → ‖A m S‖ ≤ ‖w'‖)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | 2 * R * ‖wstar‖ / Real.sqrt m +
      (1 + R * ‖wstar‖) * Real.sqrt (2 * Real.log (2 / δ) / m) <
        (D {p | p.2 * ⟪A m S, p.1⟫_ℝ ≤ 0}).toReal} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
