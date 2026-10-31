-- Prove2me | Theorems.Thm_RBMSensitivity_proposition_6_1
-- name    : RBMSensitivity.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:32.978849+00:00
-- url     : https://prove2.me/theorems/e505e3b3-31d1-4f63-a395-41d5b0206eb7
-- title:
--   Proposition 6.1 — the RBM visits every face with uniformly positive probability
-- statement:
--   Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients satisfy Assumptions 2.12 and 3.4. Given a compact subset $U_0$ of $U$ and $K,T\in(0,\infty)$, there exists $\gamma_0\in(0,1)$ such that for all $\alpha\in U_0$ and $x\in G_K$,
--   $$\mathbb P(\tau_K^{\alpha,x}(1)\le T)\ge\gamma_0.$$
--   Consequently, for each $\alpha\in U$ and $x\in G$, almost surely $\tau_K^{\alpha,x}(j)<\infty$ for all $j\in\mathbb N$.
--
--   It says that the RBM repeatedly visits every face of $G$, which is what triggers the contraction of the derivative process. The lower bound is uniform in the parameter and in the starting point of a bounded set.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: τ_K^{α,x}(j) with values in [0,∞] → visitTime in ℝ≥0∞ applied to the path s ↦ Z α x s ω; reason: the convention inf ∅ = ∞ of p.4 is built in
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Proposition 6.1, (6.2), p.22

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_Assumption_3_4
import Definitions.Def_RBMSensitivity_Data_IsRBMFamily
import Definitions.Def_RBMSensitivity_SimpleCone_visitTime
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Proposition 6.1**: arXiv:1907.00472v2, (6.2), p.22. Given a compact subset `U₀` of `U` and
`K, T ∈ (0, ∞)`, there exists `γ₀ ∈ (0, 1)` such that for all `α ∈ U₀` and `x ∈ G_K`,
`P(τ_K^{α,x}(1) ≤ T) ≥ γ₀`. Consequently, for each `α ∈ U` and `x ∈ G`, almost surely
`τ_K^{α,x}(j) < ∞` for all `j ∈ ℕ`. -/
theorem proposition_6_1 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} (hZ : D.IsRBMFamily 𝓕 P W Z) :
    (∀ U₀ : Set ℝ, IsCompact U₀ → U₀ ⊆ D.U → ∀ K T : ℝ≥0, 0 < K → 0 < T →
      ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ < 1 ∧ ∀ α ∈ U₀, ∀ x ∈ D.GK K,
        γ₀ ≤ P.real {ω | D.visitTime K (fun s => Z α x s ω) 1 ≤ T}) ∧
    ∀ K : ℝ≥0, 0 < K → ∀ α ∈ D.U, ∀ x ∈ D.G,
      ∀ᵐ ω ∂P, ∀ j, D.visitTime K (fun s => Z α x s ω) j < ⊤ := by sorry

end RBMSensitivity
