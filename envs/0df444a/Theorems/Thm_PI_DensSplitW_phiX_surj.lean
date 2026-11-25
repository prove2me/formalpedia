-- Prove2me | Theorems.Thm_PI_DensSplitW_phiX_surj
-- name    : PI.DensSplitW.phiX_surj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:34.403738+00:00
-- url     : https://prove2.me/theorems/f96b5c10-f297-5c75-8ea1-987a206c2abf
-- title:
--   Dens Split W: phi X surj
-- statement:
--   The Dens Split W construction uses the phi X surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L41-L46

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

theorem PI.DensSplitW.phiX_surj {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Function.Surjective (phiX Ph X) := by sorry
