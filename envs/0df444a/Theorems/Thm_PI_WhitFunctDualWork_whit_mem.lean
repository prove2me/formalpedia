-- Prove2me | Theorems.Thm_PI_WhitFunctDualWork_whit_mem
-- name    : PI.WhitFunctDualWork.whit_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:10.93523+00:00
-- url     : https://prove2.me/theorems/ee209f6f-9295-5634-9e63-a4886987a5c1
-- title:
--   Whit Funct Dual Work: whit mem
-- statement:
--   The Whit Funct Dual Work construction uses the whit mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L48-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WhittakerFunctionalDual/StableOfIrreducible.lean#L48-L77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WhitFunctDualWork
open Formalism.L2.SG.GGMirabolic

theorem PI.WhitFunctDualWork.whit_mem {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V)
    (ℓ : Module.Dual ℂ V) (hℓ : IsWhit ψ₀ π ℓ) :
    ℓ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := by sorry
