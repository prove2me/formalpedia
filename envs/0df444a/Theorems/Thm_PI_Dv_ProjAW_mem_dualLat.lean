-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_mem_dualLat
-- name    : PI.Dv.ProjAW.mem_dualLat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:56.362107+00:00
-- url     : https://prove2.me/theorems/8c26af9b-321b-57b5-9ff3-857b116febd4
-- title:
--   Proj AW: mem dual Lat
-- statement:
--   The Proj AW construction uses the mem dual Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/MemDualLat.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/MemDualLat.lean#L53-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] (A : HLat K)

theorem PI.Dv.ProjAW.mem_dualLat {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) (f : Module.Dual K V) :
    f ∈ Formalism.HN.dualLat M ↔ ∀ x ∈ M, f x ∈ Set.range (algebraMap (𝓞 K) K) := by sorry
