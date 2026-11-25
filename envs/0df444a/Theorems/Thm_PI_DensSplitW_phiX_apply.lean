-- Prove2me | Theorems.Thm_PI_DensSplitW_phiX_apply
-- name    : PI.DensSplitW.phiX_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:28.033872+00:00
-- url     : https://prove2.me/theorems/972b4cba-27ab-551b-90f6-74c3272fdc37
-- title:
--   Dens Split W: phi X apply
-- statement:
--   The Dens Split W construction uses the phi X apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L13-L19

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

theorem PI.DensSplitW.phiX_apply {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (X : Fin m → Fin n → K) (y : Fin n → K) (i : Fin m) :
    phiX Ph X y i = ∑ k, ∑ l, X i k * Ph k l * y l := by sorry
