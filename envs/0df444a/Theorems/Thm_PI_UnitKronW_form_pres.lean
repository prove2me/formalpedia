-- Prove2me | Theorems.Thm_PI_UnitKronW_form_pres
-- name    : PI.UnitKronW.form_pres
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:30.130191+00:00
-- url     : https://prove2.me/theorems/717c1fda-8ecc-5080-9466-bb5632cbbbd5
-- title:
--   Unit Kron W: form pres
-- statement:
--   The Unit Kron W construction uses the form pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/PosDefFormNeZero.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/PosDefFormNeZero.lean#L9-L12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Lemmata_GeneralBFactRightBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder

theorem PI.UnitKronW.form_pres {k : ℕ} {H G : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ * H * G = H) (x y : Fin k → ℂ) :
    star (G *ᵥ x) ⬝ᵥ (H *ᵥ (G *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by sorry
