-- Prove2me | Theorems.Thm_RBMSensitivity_corollary_7_4
-- name    : RBMSensitivity.corollary_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:39:25.924875+00:00
-- url     : https://prove2.me/theorems/808e7d4d-1c21-44ee-8770-5a04d0388cb5
-- title:
--   Corollary 7.4 — uniform exponential moments of the joint process
-- statement:
--   Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients satisfy Assumptions 2.12 and 3.4. For every compact set $U_0\subset U$ and relatively compact set $A\subset\mathbb X$, with $V^\alpha$ the Lyapunov function of Proposition 7.3,
--   $$\sup\big\{\mathbb E\big[V^\alpha(\Xi^{\alpha,\xi}(t))\big]:t\ge 0,\alpha\in U_0,\xi\in A\big\}<\infty.$$
--
--   These uniform moments give tightness of the occupation measures, and uniform integrability for the interchange of limits in §9.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: ‖y‖_{B^α} := min{r ≥ 0 : y ∈ rB^α} → gauge (B α) y; reason: B^α is compact, convex, symmetric with 0 in its interior; same function
--   - encoding: the supremum as a real number → a supremum in ℝ≥0∞, strictly below ⊤; reason: same claim, with no junk value
--   - reading: relatively compact set A ⊂ X → A ⊆ X bounded in E J × E J; reason: the sense of the sentence before Proposition 7.3; stronger than relative compactness in X
--   - generalization: V^α with the constants r₁, r₂ of Proposition 7.3 → any constants satisfying (7.5) on U₀; reason: the proof uses only (7.5) and a pathwise bound valid for all r₁, r₂; Proposition 7.3 provides constants, which gives the source's claim
--   - reading: §7.2 takes ‖y‖_{B^α} ≤ |y| "without loss of generality" → the normalization is not assumed; reason: on compact U₀ the norms ‖·‖_{B^α} are uniformly equivalent to |·|, and rescaling B only changes the constants
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Corollary 7.4, (7.6), p.28

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

/-- **Corollary 7.4**: arXiv:1907.00472v2, (7.6), p.28. For every compact set `U₀ ⊂ U` and relatively compact
set `A ⊂ X`, `sup{E[V^α(Ξ^{α,ξ}(t))] : t ≥ 0, α ∈ U₀, ξ ∈ A} < ∞`.

**Formalization Note.** `V^α` is that of Proposition 7.3: the statement holds for any constants satisfying
(7.5) on `U₀`, and Proposition 7.3 provides them. "Relatively compact" means bounded in `G × ℝ^J`, the sense
of the sentence before Proposition 7.3. The supremum is in `ℝ≥0∞`. -/
theorem corollary_7_4 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {U₀ : Set ℝ} (hU₀ : IsCompact U₀) (hU₀U : U₀ ⊆ D.U)
    {r₁ r₂ β₀ η₀ K₀ : ℝ} {Δ₀ : ℝ≥0} (hV : D.LyapunovDrift B P Z 𝒥 U₀ r₁ r₂ β₀ η₀ Δ₀ K₀)
    {A : Set (E J × E J)} (hA : A ⊆ D.X) (hA' : Bornology.IsBounded A) :
    (⨆ (t : ℝ≥0) (α ∈ U₀) (ξ ∈ A),
      ∫⁻ ω, ENNReal.ofReal (D.V B r₁ r₂ α (Z α ξ.1 t ω, 𝒥 α ξ t ω)) ∂P) < ⊤ := by sorry

end RBMSensitivity
