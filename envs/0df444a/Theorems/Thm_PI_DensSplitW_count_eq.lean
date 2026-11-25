-- Prove2me | Theorems.Thm_PI_DensSplitW_count_eq
-- name    : PI.DensSplitW.count_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:21.809107+00:00
-- url     : https://prove2.me/theorems/05d3bf14-ec39-5dba-b768-ac4bc236f94e
-- title:
--   Dens Split W: count eq
-- statement:
--   The Dens Split W construction uses the count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L55-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L55-L93

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

theorem PI.DensSplitW.count_eq (hF : FiberCard) (K : Type) [Field K] [Fintype K] (n m : ℕ)
    (Ph : Matrix (Fin n) (Fin n) K) (Gm : Matrix (Fin m) (Fin m) K) (hPh : IsUnit Ph.det) :
    countSplit K n m Ph Gm = Nat.card {X : Fin m → Fin n → K // LinearIndependent K X} *
      (Fintype.card K ^ (Gm.rank * (n - m)) *
        ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i)) := by sorry
