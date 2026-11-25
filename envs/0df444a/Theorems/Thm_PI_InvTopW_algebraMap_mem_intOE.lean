-- Prove2me | Theorems.Thm_PI_InvTopW_algebraMap_mem_intOE
-- name    : PI.InvTopW.algebraMap_mem_intOE
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:50.843713+00:00
-- url     : https://prove2.me/theorems/c0692aa1-2787-45c7-96e2-247ef566b3a9
-- title:
--   Inv Top W: algebra Map mem int OE
-- statement:
--   The Inv Top W construction uses the algebra Map mem int OE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L46-L50

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

theorem PI.InvTopW.algebraMap_mem_intOE {E : Type} [Field E] [NumberField E] (a : 𝓞 E) :
    algebraMap (𝓞 E) E a ∈ Formalism.UG.intOE E := by sorry
