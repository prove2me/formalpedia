-- Prove2me | Theorems.Thm_P2M_PIW_AdelClassFin_hform_swap__d33b9707c34f
-- name    : P2M_PIW_AdelClassFin_hform_swap__d33b9707c34f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:55:05.921858+00:00
-- url     : https://prove2.me/theorems/afdaff58-55f8-4894-a428-78c7237823ed
-- title:
--   P2 M PIW Adel Class Fin hform swap  d33b9707c34f: P2 M PIW Adel Class Fin hform swap  d33b9707c34f
-- statement:
--   The P2 M PIW Adel Class Fin hform swap  d33b9707c34f construction uses the P2 M PIW Adel Class Fin hform swap  d33b9707c34f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L44-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
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
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem P2M_PIW_AdelClassFin_hform_swap__d33b9707c34f (hJ : IsHerm (starRingEnd E) J) (x y : Fin m → E) :
    hform (starRingEnd E) J y x = star (hform (starRingEnd E) J x y) := by sorry

alias «PIW».«AdelClassFin».«hform_swap'» := P2M_PIW_AdelClassFin_hform_swap__d33b9707c34f
