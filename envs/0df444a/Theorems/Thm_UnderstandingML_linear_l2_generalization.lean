-- Prove2me | Theorems.Thm_UnderstandingML_linear_l2_generalization
-- name    : UnderstandingML.linear_l2_generalization
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:44:18.010208+00:00
-- url     : https://prove2.me/theorems/38bc50a3-6076-4037-8b24-c086ca46678f
-- title:
--   Theorem 26.12: for ‖x‖₂ ≤ R a.s., H = {‖w‖₂ ≤ B} and ℓ = φ(⟨w,x⟩,y) with ρ-Lipschitz φ bounded by c on [−BR,BR], w.p. ≥ 1−δ, ∀w∈H: L_D(w) ≤ L_S(w) + 2ρBR/√m + c√(2ln(2/δ)/m)
-- statement:
--   **Theorem 26.12.** Suppose that $D$ is a distribution over $X \times Y$ such that with probability $1$ we have that $\|x\|_2 \le R$. Let $H = \{w : \|w\|_2 \le B\}$ and let $\ell : H \times Z \to \mathbb{R}$ be a loss function of the form $\ell(w, (x, y)) = \varphi(\langle w, x\rangle, y)$ (26.18) such that for all $y \in Y$, $a \mapsto \varphi(a, y)$ is a $\rho$-Lipschitz function and such that $\max_{a \in [-BR, BR]}|\varphi(a, y)| \le c$. Then, for any $\delta \in (0,1)$, with probability of at least $1 - \delta$ over the choice of an i.i.d. sample of size $m$,
--   $$\forall w \in H,\quad L_D(w) \le L_S(w) + \frac{2\rho BR}{\sqrt m} + c\sqrt{\frac{2\ln(2/\delta)}{m}}.$$
--
--   Formally: $X$ a separable Hilbert space with its Borel σ-algebra, $\varphi$ jointly measurable, $m \ge 1$, $B \ge 0$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.3 p. 384, Theorem 26.12 with its proof

import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 26.12** (p. 384). Suppose that `D` is a distribution over `X × Y` such that with
probability `1` we have `‖x‖₂ ≤ R`. Let `H = {w : ‖w‖₂ ≤ B}` and let `ℓ(w, (x, y)) = φ(⟨w, x⟩, y)`
(26.18) with `a ↦ φ(a, y)` `ρ`-Lipschitz for all `y` and `max_{a ∈ [−BR, BR]} |φ(a, y)| ≤ c`. Then,
for any `δ ∈ (0, 1)`, with probability of at least `1 − δ` over the choice of an i.i.d. sample
of size `m`, `∀ w ∈ H, L_D(w) ≤ L_S(w) + 2ρBR/√m + c √(2 ln(2/δ)/m)`.
`X` is a separable Hilbert space with its Borel σ-algebra, `φ` is jointly measurable, `m ≥ 1`. -/
theorem linear_l2_generalization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Y : Type*} [MeasurableSpace Y]
    (D : Measure (E × Y)) [IsProbabilityMeasure D] (R : ℝ) (hR : D {p | R < ‖p.1‖} = 0)
    (B : ℝ) (hB : 0 ≤ B) (φ : ℝ → Y → ℝ) (hφm : Measurable (Function.uncurry φ)) (ρ : NNReal)
    (hφ : ∀ y, LipschitzWith ρ (fun a ↦ φ a y)) (c : ℝ)
    (hc : ∀ a y, |a| ≤ B * R → |φ a y| ≤ c) (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ w : E, ‖w‖ ≤ B ∧
      empRisk (fun w p ↦ φ ⟪w, p.1⟫_ℝ p.2) S w + 2 * ρ * B * R / Real.sqrt m +
        c * Real.sqrt (2 * Real.log (2 / δ) / m) < risk (fun w p ↦ φ ⟪w, p.1⟫_ℝ p.2) D w} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
