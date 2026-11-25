-- Prove2me | Theorems.Thm_PI_KLW_NO_pick
-- name    : PI.KLW.NO.pick
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:07.648719+00:00
-- url     : https://prove2.me/theorems/917d4ffc-363d-5c64-87a4-b2be67dbd5a2
-- title:
--   NO: pick
-- statement:
--   The NO construction uses the pick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneB.lean#L45-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneB.lean#L45-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO

theorem PI.KLW.NO.pick {F : Type} [Field F] (X Y r : F) (h1 : r ≠ 1) (h2 : r ^ 2 ≠ 1) (h3 : r ≠ r ^ 2) :
    (X ≠ 1 ∧ Y ≠ 1) ∨ (r * X ≠ 1 ∧ Y ≠ r) ∨ (r ^ 2 * X ≠ 1 ∧ Y ≠ r ^ 2) := by sorry
