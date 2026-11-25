-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_charP_res
-- name    : PI.LocDualGen.FpU.charP_res
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:35.352736+00:00
-- url     : https://prove2.me/theorems/2da28159-5690-40d8-bcdb-a714856ee178
-- title:
--   Fp U: char P res
-- statement:
--   The Fp U construction uses the char P res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L47-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]

theorem PI.LocDualGen.FpU.charP_res (huni : Irreducible ((l : ℕ) : 𝒪[K])) : CharP 𝓀[K] l := by sorry
