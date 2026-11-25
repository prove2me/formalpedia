-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_fix_sum
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.inst_fix_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:00.415233+00:00
-- url     : https://prove2.me/theorems/92b290cc-0bd2-417b-87c3-c0fb0fc2ff26
-- title:
--   Unitary Group Mass Formula: inst fix sum
-- statement:
--   The Unitary Group Mass Formula construction uses the inst fix sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstPlace.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstPlace.lean#L25-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula

theorem PI.ScMuExists.UnitaryGroupMassFormula.inst_fix_sum {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (T : Finset (Fin n))
    (hm : ∀ i ∈ T, m *ᵥ Pi.single i 1 = Pi.single i 1) (c : Fin n → ℂ) (hc : ∀ i ∉ T, c i = 0) :
    m *ᵥ c = c := by sorry
