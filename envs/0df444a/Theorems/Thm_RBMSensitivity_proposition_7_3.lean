-- Prove2me | Theorems.Thm_RBMSensitivity_proposition_7_3
-- name    : RBMSensitivity.proposition_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:40:20.728988+00:00
-- url     : https://prove2.me/theorems/fa0120b1-1e0c-4cbf-a2bf-6c8b3538affc
-- title:
--   Proposition 7.3 — Lyapunov drift for the discrete skeleton of the joint process
-- statement:
--   Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients satisfy Assumptions 2.12 and 3.4. Let $U_0$ be a compact subset of $U$ and define $M_0$ as in (7.2). There are constants $r_1,r_2\in(0,\infty)$, $\beta_0\in(0,1)$ and $\eta_0,\Delta_0,K_0\in(0,\infty)$ such that for each $\alpha\in U_0$, the Lyapunov function $V^\alpha:\mathbb X\to[0,\infty)$ defined by
--   $$V^\alpha(x,y):=\exp(r_1M^\alpha(x)+r_2\|y\|_{B^\alpha}),\qquad\xi=(x,y)\in\mathbb X,$$
--   satisfies
--   $$\mathbb E\big[V^\alpha(\Xi^{\alpha,\xi}(\Delta_0))\big]\le\beta_0V^\alpha(\xi)+K_0\mathbf 1\{\xi\in\mathbb X_{\Delta_0,\eta_0}\},\qquad\alpha\in U_0,\ \xi\in\mathbb X.$$
--
--   This is the uniform stability estimate of the paper. It yields exponential moments for the joint process, uniformly on compact parameter sets.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: ‖y‖_{B^α} := min{r ≥ 0 : y ∈ rB^α} → gauge (B α) y; reason: B^α is compact, convex, symmetric with 0 in its interior; same function
--   - encoding: E[V^α(Ξ(Δ_0))] as a real number → a Lebesgue integral in ℝ≥0∞ of ENNReal.ofReal V; reason: V is nonnegative; the inequality then includes finiteness
--   - reading: §7.2 takes ‖y‖_{B^α} ≤ |y| "without loss of generality" → the normalization is not assumed; reason: on compact U₀ the norms are uniformly equivalent, and rescaling only changes r₂
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Proposition 7.3, (7.4), (7.5), p.28

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_Assumption_3_4
import Definitions.Def_RBMSensitivity_Data_IsJointFamily
import Definitions.Def_RBMSensitivity_Data_LyapunovDrift
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Proposition 7.3**: arXiv:1907.00472v2, (7.4), (7.5), p.28. Let `U₀` be a compact subset of `U`. There are
constants `r_1, r_2 ∈ (0, ∞)`, `β_0 ∈ (0, 1)` and `η_0, Δ_0, K_0 ∈ (0, ∞)` such that for each `α ∈ U₀`,
`V^α(x, y) := exp(r_1 M^α(x) + r_2 ‖y‖_{B^α})` satisfies
`E[V^α(Ξ^{α,ξ}(Δ_0))] ≤ β_0 V^α(ξ) + K_0 1{ξ ∈ X_{Δ_0,η_0}}` for `α ∈ U₀`, `ξ ∈ X`.

**Formalization Note.** The normalization `‖y‖_{B^α} ≤ |y|` of §7.2 is not assumed. -/
theorem proposition_7_3 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {U₀ : Set ℝ} (hU₀ : IsCompact U₀) (hU₀U : U₀ ⊆ D.U) :
    ∃ (r₁ r₂ β₀ η₀ : ℝ) (Δ₀ : ℝ≥0) (K₀ : ℝ),
      D.LyapunovDrift B P Z 𝒥 U₀ r₁ r₂ β₀ η₀ Δ₀ K₀ := by sorry

end RBMSensitivity
