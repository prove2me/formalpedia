-- Prove2me | Theorems.Thm_UnderstandingML_multiclass_sgd_bound
-- name    : UnderstandingML.multiclass_sgd_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:53:08.470984+00:00
-- url     : https://prove2.me/theorems/259fc68a-81b6-4dad-9004-944d28c37c1d
-- title:
--   Corollary 17.2: SGD for multiclass learning with T ≥ B²ρ²/ε² and η = √(B²/(ρ²T)) has E[L^Δ_D(h_w̄)] ≤ E[L^{g-hinge}_D(w̄)] ≤ min_{‖u‖≤B} L^{g-hinge}_D(u) + ε
-- statement:
--   **Corollary 17.2.** Let $D$ be a distribution over $X \times Y$, let $\Psi : X \times Y \to \mathbb{R}^d$, and assume that for all $x, y$ we have $\|\Psi(x,y)\| \le \rho/2$. Let $B > 0$. Then, for every $\epsilon > 0$, if we run SGD for multiclass learning with $T \ge B^2\rho^2/\epsilon^2$ iterations (examples) and $\eta = \sqrt{B^2/(\rho^2 T)}$, then the output satisfies
--   $$\mathbb{E}[L^\Delta_D(h_{\bar w})] \le \mathbb{E}[L^{g\text{-}hinge}_D(\bar w)] \le \min_{u : \|u\| \le B} L^{g\text{-}hinge}_D(u) + \epsilon.$$
--
--   Formally: the SGD of Chapter 14 driven by the sample with the directions $\Psi(x,\hat y) - \Psi(x,y)$, $\hat y$ the canonical maximizer in (17.3); hypotheses as in Corollary 17.1.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.2.5 p. 235, Corollary 17.2 (from Corollary 14.12 and Claim 14.6)

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 17.2** (p. 235). Let `D` be a distribution over `X × Y`, `Ψ : X × Y → ℝ^d` with
`‖Ψ(x, y)‖ ≤ ρ/2` for all `x, y`, and `B > 0`. For every `ε > 0`, running SGD for multiclass
learning (directions `Ψ(x, ŷ) − Ψ(x, y)` with `ŷ` a maximizer in (17.3)) for `T ≥ B²ρ²/ε²`
iterations with `η = √(B²/(ρ²T))` gives
`E[L^Δ_D(h_w̄)] ≤ E[L^{g-hinge}_D(w̄)] ≤ min_{‖u‖ ≤ B} L^{g-hinge}_D(u) + ε`. Hypotheses as in
Corollary 17.1; the SGD is that of Chapter 14 driven by the sample. -/
theorem multiclass_sgd_bound {d : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [Nonempty Y] (Δ : Y → Y → ℝ)
    (hΔ : ∀ y' y, 0 ≤ Δ y' y) (hΔ0 : ∀ y, Δ y y = 0) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ x y, ‖Ψ x y‖ ≤ ρ / 2) (D : Measure (X × Y)) [IsProbabilityMeasure D] (ε : ℝ)
    (hε : 0 < ε) (T : ℕ) (hT : B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T) :
    ∫ S, risk (deltaLoss Δ Ψ) D
        (sgdAverage (B / (ρ * Real.sqrt T)) (genHingeDirection Δ Ψ) S) ∂(iidLaw D T) ≤
      ∫ S, risk (genHingeLoss Δ Ψ) D
        (sgdAverage (B / (ρ * Real.sqrt T)) (genHingeDirection Δ Ψ) S) ∂(iidLaw D T) ∧
    ∀ u : Vec d, ‖u‖ ≤ B →
      ∫ S, risk (genHingeLoss Δ Ψ) D
          (sgdAverage (B / (ρ * Real.sqrt T)) (genHingeDirection Δ Ψ) S) ∂(iidLaw D T) ≤
        risk (genHingeLoss Δ Ψ) D u + ε := by sorry

end UnderstandingML
