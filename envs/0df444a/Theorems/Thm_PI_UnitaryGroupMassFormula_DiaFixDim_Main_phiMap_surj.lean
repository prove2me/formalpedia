-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_phiMap_surj
-- name    : PI.UnitaryGroupMassFormula.DiaFixDim.Main.phiMap_surj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:47.788363+00:00
-- url     : https://prove2.me/theorems/42e2c2db-972a-460d-af91-8480778ad6b8
-- title:
--   Main: phi Map surj
-- statement:
--   The Main construction uses the phi Map surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L203-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L203-L221

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DiaFixDim PI.UnitaryGroupMassFormula.DiaFixDim.Main
open Formalism.UG Formalism.L2.SG.ClassAct Module

theorem PI.UnitaryGroupMassFormula.DiaFixDim.Main.phiMap_surj {G : Type} [Group G] (Γ K D : Subgroup G) (hN : Normalises D K) :
    Function.Surjective (phiMap Γ K D hN) := by sorry
