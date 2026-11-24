-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_low_nat
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.low_nat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:16.184821+00:00
-- url     : https://prove2.me/theorems/7059f90c-6a85-40da-ac42-6ec73308693d
-- title:
--   UJClass Fin: low nat
-- statement:
--   The UJClass Fin construction uses the low nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L134-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L134-L150

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassFin.low_nat {M : ℕ} (L : Set (Fin M → E))
    (h5 : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L := by sorry
