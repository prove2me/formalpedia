-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_dk_le
-- name    : PI.UnitaryGroupMassFormula.DiaFixDim.Main.dk_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:29.222381+00:00
-- url     : https://prove2.me/theorems/6386304d-53f8-4983-8814-fe82321e33b7
-- title:
--   Main: dk le
-- statement:
--   The Main construction uses the dk le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L31-L35

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

theorem PI.UnitaryGroupMassFormula.DiaFixDim.Main.dk_le {G : Type} [Group G] (K D K₀ : Subgroup G) (hN : Normalises D K) (hK : K ≤ K₀)
    (hD : D ≤ K₀) : dk K D hN ≤ K₀ := by sorry
