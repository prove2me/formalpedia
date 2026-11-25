-- Prove2me | Theorems.Thm_PI_FGTFG_peel
-- name    : PI.FGTFG.peel
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:06.92438+00:00
-- url     : https://prove2.me/theorems/3cfb8cdf-3037-470f-b5ec-e570144551a1
-- title:
--   FGTFG: peel
-- statement:
--   The FGTFG construction uses the peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorsionFreeGenerators/FGTorsionFreeGenOf.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorsionFreeGenerators/FGTorsionFreeGenOf.lean#L11-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_FGTorsionFreeGenOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FGTFG
open Module

theorem PI.FGTFG.peel {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M] (φ : M →ₗ[R] R) (b : R) (hb : b ≠ 0)
    (hφ : LinearMap.range φ = Ideal.span {b}) :
    finrank R (LinearMap.ker φ) + 1 = finrank R M ∧
    ∃ e : M, LinearMap.ker φ ⊔ Submodule.span R {e} = ⊤ := by sorry
