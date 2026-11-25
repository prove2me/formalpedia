-- Prove2me | Theorems.Thm_QPK_ennreal_le_one_of_pow_le
-- name    : QPK.ennreal_le_one_of_pow_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:17.027595+00:00
-- url     : https://prove2.me/theorems/c9bb00a0-80f9-4eac-86d6-d47adefb3df0
-- title:
--   QPK: ennreal le one of pow le
-- statement:
--   The QPK construction uses the ennreal le one of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L15-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK

theorem QPK.ennreal_le_one_of_pow_le {d M : ℝ≥0∞} (hdt : d ≠ ⊤) (hM : M ≠ ⊤)
    (h : ∀ k : ℕ, d ^ k ≤ M) : d ≤ 1 := by sorry
