-- Prove2me | Theorems.Thm_PI_DensSplitW_cond_iff
-- name    : PI.DensSplitW.cond_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:38.969857+00:00
-- url     : https://prove2.me/theorems/1ac87f79-ad85-44c8-946d-7848a7c0a1b3
-- title:
--   Dens Split W: cond iff
-- statement:
--   The Dens Split W construction uses the cond iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L21-L31

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

theorem PI.DensSplitW.cond_iff {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K) (X Y : Fin m → Fin n → K) :
    (∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) ↔ ∀ j, phiX Ph X (Y j) = Gm.transpose j := by sorry
