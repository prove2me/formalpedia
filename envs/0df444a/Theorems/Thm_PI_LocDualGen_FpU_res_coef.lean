-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_res_coef
-- name    : PI.LocDualGen.FpU.res_coef
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:26:37.135871+00:00
-- url     : https://prove2.me/theorems/28562c2a-c9cd-40cd-b17c-4bb254a4ebb1
-- title:
--   Fp U: res coef
-- statement:
--   The Fp U construction uses the res coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L113-L118

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
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
variable [CharP 𝓀[K] l]
attribute [local instance] algRes

theorem PI.LocDualGen.FpU.res_coef (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (y : 𝒪[K]) (j : Fin (fdim K l)) :
    (bb K l).repr (residue 𝒪[K] y) j = PadicInt.toZMod (coef K l hcont huni y j) := by sorry
