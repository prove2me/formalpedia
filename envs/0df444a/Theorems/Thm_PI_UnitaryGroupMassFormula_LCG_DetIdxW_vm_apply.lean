-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DetIdxW_vm_apply
-- name    : PI.UnitaryGroupMassFormula.LCG.DetIdxW.vm_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:05.830544+00:00
-- url     : https://prove2.me/theorems/3935b468-8ddb-4622-8f6f-00195ef31501
-- title:
--   Det Idx W: vm apply
-- statement:
--   The Det Idx W construction uses the vm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDet.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDet.lean#L31-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DetIdxW
variable {K : Type} [Field K] [NumberField K] {k : ℕ}

theorem PI.UnitaryGroupMassFormula.LCG.DetIdxW.vm_apply (M : Matrix (Fin k) (Fin k) K) (s : Fin k → K) : vm M s = s ᵥ* M := by sorry
