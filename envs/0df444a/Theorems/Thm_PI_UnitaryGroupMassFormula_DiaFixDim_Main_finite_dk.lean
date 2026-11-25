-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_finite_dk
-- name    : PI.UnitaryGroupMassFormula.DiaFixDim.Main.finite_dk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:22.539045+00:00
-- url     : https://prove2.me/theorems/cafea502-56fb-4cd0-a7a7-26b3a5cf3870
-- title:
--   Main: finite dk
-- statement:
--   The Main construction uses the finite dk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L146-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L146-L157

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

theorem PI.UnitaryGroupMassFormula.DiaFixDim.Main.finite_dk {G : Type} [Group G] (Γ K D : Subgroup G) (hN : Normalises D K)
    (hfin : Finite (ClassSet Γ K)) : Finite (ClassSet Γ (dk K D hN)) := by sorry
