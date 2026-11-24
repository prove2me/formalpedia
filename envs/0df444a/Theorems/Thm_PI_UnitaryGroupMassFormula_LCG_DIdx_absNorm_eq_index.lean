-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_absNorm_eq_index
-- name    : PI.UnitaryGroupMassFormula.LCG.DIdx.absNorm_eq_index
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:52.308954+00:00
-- url     : https://prove2.me/theorems/1a6cc644-d3ae-4f77-86b4-543e3bf4b7b3
-- title:
--   DIdx: abs Norm eq index
-- statement:
--   The DIdx construction uses the abs Norm eq index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDual.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDual.lean#L42-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
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
open PI.UnitaryGroupMassFormula.LCG.DIdx

theorem PI.UnitaryGroupMassFormula.LCG.DIdx.absNorm_eq_index {S : Type} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) : Ideal.absNorm I = I.toAddSubgroup.index := by sorry
