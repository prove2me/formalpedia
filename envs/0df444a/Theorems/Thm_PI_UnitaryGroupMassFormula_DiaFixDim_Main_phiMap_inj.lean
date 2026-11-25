-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_phiMap_inj
-- name    : PI.UnitaryGroupMassFormula.DiaFixDim.Main.phiMap_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:24.074137+00:00
-- url     : https://prove2.me/theorems/6e7318e9-5972-44e2-a5c3-064ff67fb1d3
-- title:
--   Main: phi Map inj
-- statement:
--   The Main construction uses the phi Map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L163-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L163-L201

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

theorem PI.UnitaryGroupMassFormula.DiaFixDim.Main.phiMap_inj {G : Type} [Group G] (Γ K K₀ D : Subgroup G) (hN : Normalises D K)
    (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) : Function.Injective (phiMap Γ K D hN) := by sorry
