-- Prove2me | Theorems.Thm_RBMSensitivity_theorem_3_5
-- name    : RBMSensitivity.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:02.335998+00:00
-- url     : https://prove2.me/theorems/6d87a1ed-33fc-46f3-b0a4-03c118317e46
-- title:
--   Theorem 3.5 — the RBM is positive recurrent with a unique stationary distribution
-- statement:
--   Suppose the data $\{(d_i(\cdot),n_i),i\in\mathcal I\}$ satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients $b(\cdot)$, $\sigma(\cdot)$ and $R(\cdot)$ satisfy Assumptions 2.12 and 3.4. Then for each $\alpha\in U$, $Z^\alpha$ is positive recurrent and has a unique stationary distribution.
--
--   It is the input for the statement that the RBM returns to compact sets, and it pins down the first marginal of any stationary distribution of the joint process. The paper quotes it from Budhiraja and Dupuis and from Dupuis and Williams.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: stationary distribution of Z^α on G → probability measure on E J with ν Gᶜ = 0; reason: G is closed; same objects
--   - reading: "positive recurrent" is not defined in the paper → E[τ_A] < ∞ for every x ∈ G and every closed A ⊆ G of positive Lebesgue measure; reason: the sense of Dupuis–Williams [14], the cited source
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 3.5, p.10 (cited: [8, Theorem 3.8] & [14, Theorem 2.6])

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_Assumption_3_4
import Definitions.Def_RBMSensitivity_Data_IsRBMFamily
import Definitions.Def_RBMSensitivity_Data_IsPositiveRecurrent
import Definitions.Def_RBMSensitivity_Data_IsStationaryRBM
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Theorem 3.5** ([8, Theorem 3.8] & [14, Theorem 2.6]): arXiv:1907.00472v2, p.10. Under Assumptions
2.2, 2.4, 2.5, 2.12 and 3.4, for each `α ∈ U`, `Z^α` is positive recurrent and has a unique stationary
distribution.

**Formalization Note.** "Positive recurrent" is `Data.IsPositiveRecurrent`. -/
theorem theorem_3_5 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} (hZ : D.IsRBMFamily 𝓕 P W Z)
    {α : ℝ} (hα : α ∈ D.U) :
    D.IsPositiveRecurrent P Z α ∧ ∃! ν : Measure (E J), D.IsStationaryRBM P Z α ν := by sorry

end RBMSensitivity
