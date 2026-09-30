-- Prove2me | Theorems.Thm_UnderstandingML_multiclass_svm_bound
-- name    : UnderstandingML.multiclass_svm_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:52:50.264705+00:00
-- url     : https://prove2.me/theorems/07ae9648-eb31-491b-92d9-5125b0ecee94
-- title:
--   Corollary 17.1: Multiclass SVM with λ = √(2ρ²/(B²m)) has E_S[L^Δ_D(h_w)] ≤ E_S[L^{g-hinge}_D(w)] ≤ min_{‖u‖≤B} L^{g-hinge}_D(u) + √(8ρ²B²/m) when ‖Ψ(x,y)‖ ≤ ρ/2
-- statement:
--   **Corollary 17.1.** Let $D$ be a distribution over $X \times Y$, let $\Psi : X \times Y \to \mathbb{R}^d$, and assume that for all $x \in X$ and $y \in Y$ we have $\|\Psi(x,y)\| \le \rho/2$. Let $B > 0$. Consider running Multiclass SVM with $\lambda = \sqrt{\frac{2\rho^2}{B^2 m}}$ on a training set $S \sim D^m$ and let $h_w$ be the output of Multiclass SVM. Then
--   $$\mathbb{E}_{S \sim D^m}[L^\Delta_D(h_w)] \le \mathbb{E}_{S \sim D^m}[L^{g\text{-}hinge}_D(w)] \le \min_{u : \|u\| \le B} L^{g\text{-}hinge}_D(u) + \sqrt{\frac{8\rho^2B^2}{m}},$$
--   where $L^\Delta_D(h) = \mathbb{E}_{(x,y) \sim D}[\Delta(h(x), y)]$ and $L^{g\text{-}hinge}_D(w) = \mathbb{E}_{(x,y) \sim D}[\ell(w,(x,y))]$.
--
--   Formally: for a finite label set, $\Delta \ge 0$ with $\Delta(y,y) = 0$, measurable $\Psi(\cdot, y)$, $m \ge 1$, the RLM learner for the generalized hinge loss (measurable, automatic for the unique minimizer), and the canonical argmax predictor of its output.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.2.5 pp. 234-235, Corollary 17.1 (from Corollary 13.8 and §17.2.4)

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 17.1** (pp. 234–235). Let `D` be a distribution over `X × Y`, `Ψ : X × Y → ℝ^d` with
`‖Ψ(x, y)‖ ≤ ρ/2` for all `x, y`, and `B > 0`. Consider running Multiclass SVM (the RLM rule for
the generalized hinge loss) with `λ = √(2ρ²/(B²m))` on `S ∼ D^m`, and let `h_w` be its output.
Then `E_S[L^Δ_D(h_w)] ≤ E_S[L^{g-hinge}_D(w)] ≤ min_{‖u‖ ≤ B} L^{g-hinge}_D(u) + √(8ρ²B²/m)`.
Stated for a finite label set with `Δ ≥ 0`, `Δ(y, y) = 0`, measurable `Ψ(·, y)`, `m ≥ 1`, and a
measurable RLM learner (automatic for the unique minimizer). -/
theorem multiclass_svm_bound {d : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [Nonempty Y] (Δ : Y → Y → ℝ)
    (hΔ : ∀ y' y, 0 ≤ Δ y' y) (hΔ0 : ∀ y, Δ y y = 0) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ x y, ‖Ψ x y‖ ≤ ρ / 2) (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (A : Learner (X × Y) (Vec d))
    (hA : ∀ (m : ℕ) (S : Fin m → X × Y),
      IsRLM (genHingeLoss Δ Ψ) (Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * m))) S (A m S))
    (hAmeas : ∀ m, Measurable (A m)) (m : ℕ) (hm : 0 < m) :
    ∫ S, risk (deltaLoss Δ Ψ) D (A m S) ∂(iidLaw D m) ≤
        ∫ S, risk (genHingeLoss Δ Ψ) D (A m S) ∂(iidLaw D m) ∧
    ∀ u : Vec d, ‖u‖ ≤ B →
      ∫ S, risk (genHingeLoss Δ Ψ) D (A m S) ∂(iidLaw D m) ≤
        risk (genHingeLoss Δ Ψ) D u + Real.sqrt (8 * ρ ^ 2 * B ^ 2 / m) := by sorry

end UnderstandingML
