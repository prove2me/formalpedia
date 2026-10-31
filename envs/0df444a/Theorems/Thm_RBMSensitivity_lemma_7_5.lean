-- Prove2me | Theorems.Thm_RBMSensitivity_lemma_7_5
-- name    : RBMSensitivity.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:40.975715+00:00
-- url     : https://prove2.me/theorems/7a6e36ab-796e-43d2-b88b-fd12f71d752f
-- title:
--   Lemma 7.5 — pathwise bound on the derivative process
-- statement:
--   Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients satisfy Assumptions 2.12 and 3.4. Let $U_0$ be a compact subset of $U$ and $\delta_0\in[0,1)$ the contraction coefficient from Lemma 4.20. There exists $C_{\mathcal J}\in(0,\infty)$ such that for $\alpha\in U_0$, $\xi=(x,y)\in\mathbb X$ and $T<\infty$,
--   $$\|\mathcal J^{\alpha,\xi}(T)\|_{B^\alpha}\le\delta_0^{\mathbf 1\{\tau^{\alpha,x}(1)\le T\}}\|y\|_{B^\alpha}+C_{\mathcal J}(T+\|W\|_T).$$
--
--   It is the pathwise form in which the contraction of §4 enters the Lyapunov analysis.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: ‖y‖_{B^α} := min{r ≥ 0 : y ∈ rB^α} → gauge (B α) y; reason: B^α is compact, convex, symmetric with 0 in its interior; same function
--   - reading: no "a.s." is printed → almost surely, for all T simultaneously; reason: a pathwise bound on a process; the proof gives this
--   - reading: ‖W‖_T is not defined in the paper → sup_{0≤s≤T}|W(s)|; reason: what the proof of Lemma 7.7 computes
--   - encoding: U₀ fixed on p.28 and δ₀ from Lemma 4.20 → any compact U₀ ⊆ U and any δ₀ ∈ [0,1) satisfying (4.12) on U₀; reason: this is the content of the paper's fixing of U₀ and δ₀
--   - reading: §7.2 takes ‖y‖_{B^α} ≤ |y| "without loss of generality" → the normalization is not assumed; reason: on compact U₀ the norms ‖·‖_{B^α} are uniformly equivalent to |·|, and rescaling B only changes the constants
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Lemma 7.5, (7.7), p.29

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_Assumption_3_4
import Definitions.Def_RBMSensitivity_Data_IsJointFamily
import Definitions.Def_RBMSensitivity_Data_ContractionBound
import Definitions.Def_RBMSensitivity_SimpleCone_visitTime
import Definitions.Def_RBMSensitivity_pathSup
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Lemma 7.5**: arXiv:1907.00472v2, (7.7), p.29. There exists `C_𝒥 ∈ (0, ∞)` such that for `α ∈ U₀` and
`ξ = (x, y) ∈ X`, and `T < ∞`,
`‖𝒥^{α,ξ}(T)‖_{B^α} ≤ δ₀^{1{τ^{α,x}(1) ≤ T}} ‖y‖_{B^α} + C_𝒥 (T + ‖W‖_T)`.

**Formalization Note.** `U₀` is the compact set fixed on p.28, `δ₀` is from Lemma 4.20, and `τ^{α,x}(1)` is
the case `K = ∞`. The bound is pathwise, stated almost surely and for all `T` simultaneously (reading
R1). `‖W‖_T` is `pathSup`. -/
theorem lemma_7_5 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {U₀ : Set ℝ} (hU₀ : IsCompact U₀) (hU₀U : U₀ ⊆ D.U)
    {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ < 1) (hδ : D.ContractionBound B U₀ δ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ U₀, ∀ ξ ∈ D.X, ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      gauge (B α) (𝒥 α ξ T ω) ≤
        (if D.visitTime ⊤ (fun s => Z α ξ.1 s ω) 1 ≤ T then δ₀ else 1) * gauge (B α) ξ.2 +
          C * (T + pathSup W T ω) := by sorry

end RBMSensitivity
