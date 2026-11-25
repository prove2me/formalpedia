-- Prove2me | Theorems.Thm_PIW_AdelClassFin_units_mod_sq
-- name    : PIW.AdelClassFin.units_mod_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:05.160247+00:00
-- url     : https://prove2.me/theorems/59f3fe2f-3b40-4555-a098-bdb8f7704cd9
-- title:
--   Adel Class Fin: units mod sq
-- statement:
--   The Adel Class Fin construction uses the units mod sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/UnitsModSq.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/UnitsModSq.lean#L10-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_UnitsModSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField NumberField.Units

theorem PIW.AdelClassFin.units_mod_sq (F : Type) [Field F] [NumberField F] :
    ∃ U : Set F, U.Finite ∧ ∀ c : (𝓞 F)ˣ, ∃ w ∈ U, ∃ v : (𝓞 F)ˣ,
      algebraMap (𝓞 F) F (c : 𝓞 F) = w * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2 := by sorry
