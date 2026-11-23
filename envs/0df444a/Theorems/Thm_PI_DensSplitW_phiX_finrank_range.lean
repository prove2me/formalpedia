-- Prove2me | Theorems.Thm_PI_DensSplitW_phiX_finrank_range
-- name    : PI.DensSplitW.phiX_finrank_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:36.221588+00:00
-- url     : https://prove2.me/theorems/24c9224b-b2d5-446c-a6c4-d192346d424e
-- title:
--   Dens Split W: phi X finrank range
-- statement:
--   The Dens Split W construction uses the phi X finrank range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L33-L39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW

theorem PI.DensSplitW.phiX_finrank_range {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Module.finrank K (LinearMap.range (phiX Ph X)) = m := by sorry
