-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_nset_isMatGroup
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.nset_isMatGroup
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:42.38108+00:00
-- url     : https://prove2.me/theorems/606c4fd7-236d-4bd8-9a96-d27a58db1be4
-- title:
--   Unitary Group Mass Formula: nset is Mat Group
-- statement:
--   The Unitary Group Mass Formula construction uses the nset is Mat Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/NonstandardUnimodularLattice.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/NonstandardUnimodularLattice.lean#L16-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.nset_isMatGroup (k r : ℕ) : IsMatGroup (Nset k r) := by sorry
