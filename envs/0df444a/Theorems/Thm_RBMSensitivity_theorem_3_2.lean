-- Prove2me | Theorems.Thm_RBMSensitivity_theorem_3_2
-- name    : RBMSensitivity.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:34.536458+00:00
-- url     : https://prove2.me/theorems/3096c1ad-004a-47fd-8f93-7dbf49237c3e
-- title:
--   Theorem 3.2 — the joint process is Markov and Feller continuous
-- statement:
--   Suppose the data $\{(d_i(\cdot),n_i),i\in\mathcal I\}$ satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients $b(\cdot)$, $\sigma(\cdot)$ and $R(\cdot)$ satisfy Assumption 2.12. For each $\alpha\in U$, the family of transition functions $\{P_t^\alpha\}$ is Markovian and Feller continuous. Here $\{P_t^\alpha\}$ is **Markovian** if for every bounded measurable $\zeta:\mathbb X\to\mathbb R$ and $s,t>0$, $\mathbb E[\zeta(\Xi(s+t))\mid\mathcal F_s]=\mathbb E[\zeta(\Xi(s+t))\mid\Xi(s)]$, and **Feller continuous** if for every bounded continuous $\zeta:\mathbb X\to\mathbb R$ and $t>0$, the mapping
--   $$\xi\mapsto(P_t^\alpha\zeta)(\xi):=\int_{\mathbb X}\zeta(\tilde\xi)P_t^\alpha(\xi,d\tilde\xi)$$
--   is continuous.
--
--   The Feller property is what the existence proof for a stationary distribution uses, and it is nontrivial here because the derivative process has jumps.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - generalization: E[ζ(Ξ(s+t)) | F_s] = E[ζ(Ξ(s+t)) | Ξ(s)] → E[ζ(Ξ(s+t)) | F_s] = (P_t ζ)(Ξ(s)); reason: with the measurability clause the right side is σ(Ξ(s))-measurable, so the tower property gives the printed form; the proof gives this form, and Corollary 7.4 and Theorem 8.1 need it
--   - generalization: measurability of ξ ↦ P_t(ξ, A) is left implicit → an explicit clause: it is measurable on X; reason: needed for (3.2) to define a transition function and for Definition 3.3; dropping the clause gives the source's claim
--   - encoding: ζ : X → ℝ → ζ : E J × E J → ℝ, measurable and bounded, or continuous and bounded on X; reason: X is Borel, so a bounded Borel function on X extends; Feller is on X in the subspace topology
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 3.2, p.9

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_IsJointFamily
import Definitions.Def_RBMSensitivity_jointTransition
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Theorem 3.2**: arXiv:1907.00472v2, p.9. Under Assumptions 2.2, 2.4, 2.5 and 2.12, for each `α ∈ U` the
family of transition functions `{P_t^α}` is Markovian and Feller continuous.

**Formalization Note.** The Markov clause is stated with the transition function,
`E[ζ(Ξ(s + t)) | F_s] = (P_t^α ζ)(Ξ(s))`. With the measurability clause it implies the
printed form `E[ζ(Ξ(s + t)) | F_s] = E[ζ(Ξ(s + t)) | Ξ(s)]`. A bounded Borel `ζ` on the Borel set `X` is
the restriction of a bounded Borel function on the product. Feller continuity is on `X` in the subspace
topology, for `ζ` bounded and continuous on `X` only, since `X` is not closed (Remark 3.1). -/
theorem theorem_3_2 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {α : ℝ} (hα : α ∈ D.U) :
    (∀ ξ ∈ D.X, ∀ s t : ℝ≥0, 0 < s → 0 < t → ∀ ζ : E J × E J → ℝ, Measurable ζ →
      (∃ C : ℝ, ∀ p, |ζ p| ≤ C) →
      P[fun ω => ζ (Z α ξ.1 (s + t) ω, 𝒥 α ξ (s + t) ω) | 𝓕 s] =ᵐ[P] fun ω =>
        ∫ ω', ζ (Z α (Z α ξ.1 s ω) t ω', 𝒥 α (Z α ξ.1 s ω, 𝒥 α ξ s ω) t ω') ∂P) ∧
    (∀ t : ℝ≥0, 0 < t → ∀ ζ : E J × E J → ℝ, ContinuousOn ζ D.X →
      (∃ C : ℝ, ∀ p ∈ D.X, |ζ p| ≤ C) →
      ContinuousOn (fun ξ => ∫ ω, ζ (Z α ξ.1 t ω, 𝒥 α ξ t ω) ∂P) D.X) ∧
    ∀ (t : ℝ≥0) (A : Set (E J × E J)), MeasurableSet A →
      Measurable fun ξ : D.X => jointTransition P Z 𝒥 α t ξ A := by sorry

end RBMSensitivity
