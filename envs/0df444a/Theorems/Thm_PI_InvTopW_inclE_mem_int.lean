-- Prove2me | Theorems.Thm_PI_InvTopW_inclE_mem_int
-- name    : PI.InvTopW.inclE_mem_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:51.853011+00:00
-- url     : https://prove2.me/theorems/6e0ce088-f284-59e8-9b33-b81c0c56f5a9
-- title:
--   Inv Top W: incl E mem int
-- statement:
--   The Inv Top W construction uses the incl E mem int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L140-L145

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.InvTopW.inclE_mem_int (x : E) (hx : x ∈ Formalism.UG.intOE E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x ∈ Formalism.MainNotions.S.IntAf F E := by sorry
