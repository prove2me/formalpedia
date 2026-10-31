-- Prove2me | Theorems.Thm_RBMSensitivity_proposition_4_25
-- name    : RBMSensitivity.proposition_4_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:33.749987+00:00
-- url     : https://prove2.me/theorems/eb354a51-d8ef-49fc-8c83-4766990237c1
-- title:
--   Proposition 4.25 — contraction of solutions to the derivative problem (corrected: $\alpha\in U_0$)
-- statement:
--   Let the data satisfy Assumptions 2.2, 2.4 and 2.5. Given a compact subset $U_0$ of $U$, let $\delta_0\in[0,1)$ be as in Lemma 4.20. Let $\alpha\in U_0$, $f\in\mathbb C_G(\mathbb R^J)$ and $\psi\in\mathbb C(\mathbb R^J)$, and suppose $(h,g)$ is the solution to the SP $\{(d_i(\alpha),n_i),i\in\mathcal I\}$ for $f$ and $(\phi,\eta)$ is the solution to the derivative problem along $h$ for $\psi$. Then for all $0\le S<T<\infty$,
--   $$\|\phi(T)\|_{B^\alpha}\le\delta_0^{\mathbf 1\{\cup_{t\in[S,T]}\mathcal I(h(t))=\mathcal I\}}\|\phi(S)\|_{B^\alpha}+\kappa_\Lambda(\alpha)\sup_{S\le u\le T}\|\psi(u)-\psi(S)\|_{B^\alpha}.$$
--
--   This is the main result of §4.4: a solution of the derivative problem contracts over an interval in which the path visits every face, up to the oscillation of the input. It carries the deterministic contraction of Lemma 4.20 to the derivative process.
--
--   Differences from the source:
--   - correction: Let α ∈ U → α ∈ U₀; reason: the proof uses Lemma 4.20, which covers only U₀, and the printed form is false. Counterexample satisfying every assumption of the paper: J = 2, G = ℝ²₊, n_i = e_i, U = (−1, 1), d₁(α) = (1, −α²), d₂(α) = (−α², 1), a = E₂, b(α) = (−1, −1), U₀ = {0}, δ₀ = 0, α = 1/2; with h moving from the interior to F₁ only, then to F₂ only, ending on F₂ at T, ψ constant and φ(S) = (1, 0), one gets φ(T) = (1/16, 0) ≠ 0 while the right side of (4.20) is 0
--   - encoding: ‖y‖_{B^α} := min{r ≥ 0 : y ∈ rB^α} → gauge (B α) y; reason: B^α is compact, convex, symmetric with 0 in its interior; same function
--   - encoding: δ₀^{1{…}} → if … then δ₀ else 1; reason: same value, with δ₀^0 = 1 also at δ₀ = 0
--   - encoding: δ₀ as in Lemma 4.20 and κ_Λ of Proposition 4.15 → any δ₀ ∈ [0,1) satisfying (4.12) on U₀, and an existential κΛ : ℝ → ℝ before U₀; reason: this is the content of "as in"; Proposition 4.15's constant depends on α alone
--   - encoding: the solution (h, g) to the SP and the solution (φ, η) to the derivative problem → any such solutions; reason: both are unique when they exist (the SP under Assumptions 2.4 and 2.5; the derivative problem by (4.8) with ψ₁ = ψ₂), so the statement is the same
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Proposition 4.25, (4.20), p.17

import Mathlib
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_ContractionBound
import Definitions.Def_RBMSensitivity_Data_IsSPSolution
import Definitions.Def_RBMSensitivity_Data_IsDerivProblemSolution
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Proposition 4.25**: arXiv:1907.00472v2, (4.20), p.17, corrected to `α ∈ U₀`.

Given a compact subset `U₀` of `U`, let `δ₀ ∈ [0, 1)` be as in Lemma 4.20. For `α ∈ U₀`, `f ∈ C_G(ℝ^J)` and
`ψ ∈ C(ℝ^J)`, if `(h, g)` solves the SP for `f` and `(φ, η)` solves the derivative problem along `h` for
`ψ`, then for all `0 ≤ S < T < ∞`,
`‖φ(T)‖_{B^α} ≤ δ₀^{1{∪_{t ∈ [S,T]} I(h(t)) = I}} ‖φ(S)‖_{B^α} + κ_Λ(α) sup_{S ≤ u ≤ T} ‖ψ(u) - ψ(S)‖_{B^α}`.

**Formalization Note.** The paper prints `α ∈ U`, but its proof applies Lemma 4.20, which covers only
`α ∈ U₀`, and the printed form is false (see the item's description). `κ_Λ` is the constant of Proposition
4.15, a function of `α` alone, so its existential precedes `U₀`. The exponent is an `if`, because
`δ₀ = 0` is allowed and then `δ₀^0 = 1` must hold. The supremum is of a continuous function on the compact
nonempty `[S, T]`. -/
theorem proposition_4_25 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5) :
    ∃ κΛ : ℝ → ℝ, (∀ α, 0 ≤ κΛ α) ∧
      ∀ U₀ : Set ℝ, IsCompact U₀ → U₀ ⊆ D.U → ∀ δ₀ : ℝ, 0 ≤ δ₀ → δ₀ < 1 →
        D.ContractionBound B U₀ δ₀ →
        ∀ α ∈ U₀, ∀ f h g ψ φ η : ℝ≥0 → E J, D.IsSPSolution α f h g → Continuous ψ →
          D.IsDerivProblemSolution α h ψ φ η → ∀ S T : ℝ≥0, S < T →
            gauge (B α) (φ T) ≤
              (if (⋃ t ∈ Set.Icc S T, D.I (h t)) = Set.univ then δ₀ else 1) * gauge (B α) (φ S) +
                κΛ α * ⨆ u : Set.Icc S T, gauge (B α) (ψ u - ψ S) := by sorry

end RBMSensitivity
