-- Prove2me | Theorems.Thm_UnderstandingML_generalized_hinge_properties
-- name    : UnderstandingML.generalized_hinge_properties
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:52:06.213829+00:00
-- url     : https://prove2.me/theorems/0d63ae55-dbe2-445a-b203-ceaef52c53ef
-- title:
--   §17.2.4: the generalized hinge loss upper bounds Δ(h_w(x), y), with equality under margins ≥ Δ, is convex in w and ρ-Lipschitz with ρ = max_{y'} ‖Ψ(x,y') − Ψ(x,y)‖
-- statement:
--   **§17.2.4 (Generalized hinge loss).** For $\ell(w,(x,y)) = \max_{y' \in Y}(\Delta(y',y) + \langle w, \Psi(x,y') - \Psi(x,y)\rangle)$ (17.3): $\ell(w,(x,y)) \ge \Delta(h_w(x), y)$; equality holds whenever the score of the correct label is larger than the score of any other label $y'$ by at least $\Delta(y',y)$; $\ell(w,(x,y))$ is convex with respect to $w$ (a maximum of linear functions); and it is $\rho$-Lipschitz with $\rho = \max_{y'}\|\Psi(x,y') - \Psi(x,y)\|$.
--
--   Formally: the first two clauses hold for every argmax predictor $h_w$, the second given $\Delta(y,y) = 0$.
--
--   The equality clause assumes the book's standing conditions on the cost, $\Delta \ge 0$ and $\Delta(y, y) = 0$ (§17.2.2: $\Delta : Y \times Y \to \mathbb{R}_+$). Without $\Delta \ge 0$ it fails: with two labels, $\Delta(b, a) = -1$, scores $\langle w, \Psi(x, b)\rangle = 1/2$ and $\langle w, \Psi(x, a)\rangle = 0$, and correct label $a$, the margin condition holds, the argmax is $b$, and $\ell = 0 \ne -1 = \Delta(b, a)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.2.4 pp. 233-234, Equation (17.3) and the properties stated after it

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **§17.2.4, Equation (17.3)** (p. 233). The generalized hinge loss
`ℓ(w, (x, y)) = max_{y'} (Δ(y', y) + ⟨w, Ψ(x, y') − Ψ(x, y)⟩)` satisfies `ℓ(w, (x, y)) ≥ Δ(h_w(x), y)` for
every argmax predictor `h_w`; equality holds whenever the score of the correct label exceeds the
score of every other label `y'` by at least `Δ(y', y)` (given the book's `Δ ≥ 0` and
`Δ(y, y) = 0`; with a negative `Δ(y', y)` an argmax `y'` has `Δ(y', y) < 0 = ℓ`); `ℓ(w, (x, y))` is
convex in `w`; and it is `ρ`-Lipschitz in `w` with `ρ = max_{y'} ‖Ψ(x, y') − Ψ(x, y)‖`. -/
theorem generalized_hinge_properties {d : ℕ} {X Y : Type*} [Fintype Y] [Nonempty Y]
    (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) :
    (∀ h : X → Y, IsArgmaxPredictor Ψ w h → Δ (h z.1) z.2 ≤ genHingeLoss Δ Ψ w z) ∧
    ((∀ y', 0 ≤ Δ y' z.2) → Δ z.2 z.2 = 0 →
      (∀ y', y' ≠ z.2 → ⟪w, Ψ z.1 y'⟫_ℝ + Δ y' z.2 ≤ ⟪w, Ψ z.1 z.2⟫_ℝ) →
      ∀ h : X → Y, IsArgmaxPredictor Ψ w h → genHingeLoss Δ Ψ w z = Δ (h z.1) z.2) ∧
    ConvexOn ℝ Set.univ (fun w ↦ genHingeLoss Δ Ψ w z) ∧
    ∀ w₁ w₂ : Vec d, |genHingeLoss Δ Ψ w₁ z - genHingeLoss Δ Ψ w₂ z| ≤
      (⨆ y' : Y, ‖Ψ z.1 y' - Ψ z.1 z.2‖) * ‖w₁ - w₂‖ := by sorry

end UnderstandingML
