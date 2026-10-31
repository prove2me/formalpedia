-- Prove2me | Theorems.Thm_RBMSensitivity_theorem_3_6
-- name    : RBMSensitivity.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:30.47712+00:00
-- url     : https://prove2.me/theorems/ce758186-0f09-4441-bd1a-3eaace30f3af
-- title:
--   Theorem 3.6 — existence and uniqueness of the stationary distribution of the joint process
-- statement:
--   Suppose the data $\{(d_i(\cdot),n_i),i\in\mathcal I\}$ satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients $b(\cdot)$, $\sigma(\cdot)$ and $R(\cdot)$ satisfy Assumptions 2.12 and 3.4. For each $\alpha\in U$ there exists a unique stationary distribution of the joint process $\Xi^\alpha=(Z^\alpha,\mathcal J^\alpha)$ associated with $\alpha$.
--
--   It gives the random variable $\Xi^\alpha(\infty)=(Z^\alpha(\infty),\mathcal J^\alpha(\infty))$ of the goal theorem, and it is one of the three main contributions of the paper.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: probability measure on (X, B(X)) → probability measure on E J × E J with ν Xᶜ = 0, tested on Borel subsets of the product; reason: X is Borel in the product and the joint process stays in X a.s.; same objects
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 3.6, p.10

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

/-- **Theorem 3.6**: arXiv:1907.00472v2, p.10. Under Assumptions 2.2, 2.4, 2.5, 2.12 and 3.4, for each `α ∈ U`
there exists a unique stationary distribution of the joint process `Ξ^α = (Z^α, 𝒥^α)` associated with `α`. -/
theorem theorem_3_6 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {α : ℝ} (hα : α ∈ D.U) :
    ∃! ν : Measure (E J × E J), D.IsStationaryJoint P Z 𝒥 α ν := by sorry

end RBMSensitivity
