-- Prove2me | Theorems.Thm_RBMSensitivity_corollary_2_16
-- name    : RBMSensitivity.corollary_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:22.341133+00:00
-- url     : https://prove2.me/theorems/b2b24d0d-6f4b-4e6a-bd5a-f5eba6c7202f
-- title:
--   Corollary 2.16 — finite-horizon sensitivities via the derivative process
-- statement:
--   Let $\zeta_1,\zeta_2:G\to\mathbb R$ be continuously differentiable functions with bounded first partial derivatives. For $t>0$ define
--   $$\Theta_t(\alpha):=\mathbb E\Big[\int_0^t\zeta_1(Z^{\alpha,x}(s))\,ds+\zeta_2(Z^{\alpha,x}(t))\Big],\qquad\alpha\in U.$$
--   Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5 and the coefficients satisfy Assumption 2.12, and let $x\in G$. Then for each $t>0$ and $\alpha\in U$, $\Theta_t$ is differentiable at $\alpha$ and
--   $$\Theta_t'(\alpha)=\mathbb E\Big[\int_0^t\zeta_1'(Z^{\alpha,x}(s))\mathcal J^{\alpha,\xi}(s)\,ds+\zeta_2'(Z^{\alpha,x}(t))\mathcal J^{\alpha,\xi}(t)\Big],$$
--   where $\xi=(x,0)$.
--
--   This is the finite-horizon sensitivity formula. The goal theorem is its infinite-horizon analogue. It is quoted in the paper from Lipshutz and Ramanan's earlier work.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: f : G → ℝ continuously differentiable with bounded continuous Jacobian f' on G → f : E J → ℝ, ContDiffOn ℝ 1 f G, bound on fderivWithin ℝ f G; reason: G is closed and convex with nonempty interior, so it has unique derivatives and fderivWithin is f'; values of f off G are never used
--   - reading: ξ is not named in the corollary → ξ = (x, 0); reason: Θ_t perturbs α only, and §9 applies the corollary with ξ = (x, 0)
--   - generalization: the expectations are written without comment → the conclusion also asserts integrability of both integrands; reason: true by the bounds on Z and J; it rules out the junk value of a Bochner integral, and dropping those clauses gives the source's claim
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Corollary 2.16, p.8 (cited: [25, Corollary 3.16])

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_IsJointFamily
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Corollary 2.16** ([25, Corollary 3.16]): arXiv:1907.00472v2, p.8. Let `ζ₁, ζ₂ : G → ℝ` be C¹ with
bounded first partial derivatives, and `Θ_t(α) := E[∫_0^t ζ₁(Z^{α,x}(s)) ds + ζ₂(Z^{α,x}(t))]`. Then for
each `t > 0` and `α ∈ U`, `Θ_t` is differentiable at `α` with
`Θ'_t(α) = E[∫_0^t ζ₁'(Z^{α,x}(s)) 𝒥^{α,ξ}(s) ds + ζ₂'(Z^{α,x}(t)) 𝒥^{α,ξ}(t)]`.

**Formalization Note.** `ξ` is `(x, 0)`: `Θ_t` perturbs `α` only. The integrability clauses
guard against the junk value `0` of a Bochner integral. -/
theorem corollary_2_16 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {ζ₁ ζ₂ : E J → ℝ} (hζ₁ : ContDiffOn ℝ 1 ζ₁ D.G) (hζ₂ : ContDiffOn ℝ 1 ζ₂ D.G)
    (hζ₁' : ∃ C, ∀ x ∈ D.G, ‖fderivWithin ℝ ζ₁ D.G x‖ ≤ C)
    (hζ₂' : ∃ C, ∀ x ∈ D.G, ‖fderivWithin ℝ ζ₂ D.G x‖ ≤ C)
    {x : E J} (hx : x ∈ D.G) {t : ℝ≥0} (ht : 0 < t) {α : ℝ} (hα : α ∈ D.U) :
    Integrable (fun ω => (∫ s in (0 : ℝ)..t, ζ₁ (Z α x s.toNNReal ω)) + ζ₂ (Z α x t ω)) P ∧
    Integrable (fun ω =>
      (∫ s in (0 : ℝ)..t,
        fderivWithin ℝ ζ₁ D.G (Z α x s.toNNReal ω) (𝒥 α (x, 0) s.toNNReal ω)) +
      fderivWithin ℝ ζ₂ D.G (Z α x t ω) (𝒥 α (x, 0) t ω)) P ∧
    HasDerivAt
      (fun β => ∫ ω, (∫ s in (0 : ℝ)..t, ζ₁ (Z β x s.toNNReal ω)) + ζ₂ (Z β x t ω) ∂P)
      (∫ ω, (∫ s in (0 : ℝ)..t,
          fderivWithin ℝ ζ₁ D.G (Z α x s.toNNReal ω) (𝒥 α (x, 0) s.toNNReal ω)) +
        fderivWithin ℝ ζ₂ D.G (Z α x t ω) (𝒥 α (x, 0) t ω) ∂P) α := by sorry

end RBMSensitivity
