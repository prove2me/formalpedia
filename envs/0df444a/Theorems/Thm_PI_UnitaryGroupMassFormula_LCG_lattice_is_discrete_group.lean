-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_lattice_is_discrete_group
-- name    : PI.UnitaryGroupMassFormula.LCG.lattice_is_discrete_group
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:21.066842+00:00
-- url     : https://prove2.me/theorems/14ea889a-3651-585a-8e63-152e509449e1
-- title:
--   LCG: lattice is discrete group
-- statement:
--   The LCG construction uses the lattice is discrete group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatticeIsDiscreteGroup.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatticeIsDiscreteGroup.lean#L17-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatticeIsDiscreteGroup
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
open PI.LatCountG

theorem PI.UnitaryGroupMassFormula.LCG.lattice_is_discrete_group : LatIsG := by sorry
