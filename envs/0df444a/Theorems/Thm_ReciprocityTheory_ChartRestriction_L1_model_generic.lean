-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_model_generic
-- name    : ReciprocityTheory.ChartRestriction.L1.model_generic
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:11:22.152789+00:00
-- url     : https://prove2.me/theorems/930dbc42-09bc-5cf4-a3f6-a5dc0c06387c
-- title:
--   L1: model generic
-- statement:
--   The L1 construction uses the model generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedModel.lean#L42-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedModel.lean#L42-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKur
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedModel
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.model_generic (h5 : 5 ≤ l) (a b J : ℂ_[l]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : a ^ 3 - 27 * b ^ 2 ≠ 0) (hJe : J = 1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
    (hJ : J ∈ MaximalUnramifiedExtension l) (hJ1 : ‖J‖ ≤ 1) (m n : ℤ) (hm : ‖J‖ = (l : ℝ) ^ (3 * m))
    (hn : ‖J - 1728‖ = (l : ℝ) ^ (2 * n)) :
    ∃ g2 g3 : ℂ_[l], g2 ∈ MaximalUnramifiedExtension l ∧ g3 ∈ MaximalUnramifiedExtension l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1 ∧
      ∃ lam : ℂ_[l], lam ≠ 0 ∧ g2 = lam ^ 4 * a ∧ g3 = lam ^ 6 * b := by sorry
