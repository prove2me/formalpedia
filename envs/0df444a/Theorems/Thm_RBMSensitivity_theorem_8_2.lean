-- Prove2me | Theorems.Thm_RBMSensitivity_theorem_8_2
-- name    : RBMSensitivity.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:12.386045+00:00
-- url     : https://prove2.me/theorems/7475a2f7-d929-49f1-b7b6-2ce39d7644da
-- title:
--   Theorem 8.2 — at most one stationary distribution of the joint process
-- statement:
--   Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients satisfy Assumptions 2.12 and 3.4. For each $\alpha\in U$ there is at most one stationary distribution for the joint process $\Xi^\alpha$.
--
--   Uniqueness makes $(Z^\alpha(\infty),\mathcal J^\alpha(\infty))$ well defined in law, and it is what identifies every limit of the time averages in §9.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: probability measure on (X, B(X)) → probability measure on E J × E J with ν Xᶜ = 0, tested on Borel subsets of the product; reason: X is Borel in the product and the joint process stays in X a.s.; same objects
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 8.2, p.34

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_Assumption_3_4
import Definitions.Def_RBMSensitivity_Data_IsJointFamily
import Definitions.Def_RBMSensitivity_Data_IsStationaryJoint
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Theorem 8.2**: arXiv:1907.00472v2, p.34. For each `α ∈ U` there is at most one stationary distribution
for the joint process `Ξ^α`. §8 assumes 2.2, 2.4, 2.5, 2.12 and 3.4 throughout (p.33). -/
theorem theorem_8_2 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {α : ℝ} (hα : α ∈ D.U) {ν₁ ν₂ : Measure (E J × E J)}
    (hν₁ : D.IsStationaryJoint P Z 𝒥 α ν₁) (hν₂ : D.IsStationaryJoint P Z 𝒥 α ν₂) :
    ν₁ = ν₂ := by sorry

end RBMSensitivity
