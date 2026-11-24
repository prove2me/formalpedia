-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_neat_one
-- name    : PI.UnitaryGroupMassFormula.DiaFixDim.Main.neat_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:21.5918+00:00
-- url     : https://prove2.me/theorems/38b3f5af-f846-4037-9df5-35478e17fce7
-- title:
--   Main: neat one
-- statement:
--   The Main construction uses the neat one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean#L120-L124

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

theorem PI.UnitaryGroupMassFormula.DiaFixDim.Main.neat_one {G : Type} [Group G] {Γ K₀ : Subgroup G} (hn : IsNeat Γ K₀) {x γ : G}
    (hγ : γ ∈ Γ) (h : x⁻¹ * γ * x ∈ K₀) : γ = 1 := by sorry
