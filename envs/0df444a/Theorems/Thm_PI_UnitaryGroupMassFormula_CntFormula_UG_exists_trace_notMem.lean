-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_trace_notMem
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.exists_trace_notMem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:06.778744+00:00
-- url     : https://prove2.me/theorems/9da2ad4d-562b-4c8e-b88b-811f80da8c1e
-- title:
--   UG: exists trace not Mem
-- statement:
--   The UG construction uses the exists trace not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsTraceNotMem.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsTraceNotMem.lean#L93-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_PairUnitLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsTraceNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.exists_trace_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ l : 𝓞 K, l + conjO K l ∉ p := by sorry
