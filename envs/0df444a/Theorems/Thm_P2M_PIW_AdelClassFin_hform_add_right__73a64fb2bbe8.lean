-- Prove2me | Theorems.Thm_P2M_PIW_AdelClassFin_hform_add_right__73a64fb2bbe8
-- name    : P2M_PIW_AdelClassFin_hform_add_right__73a64fb2bbe8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:28:32.778657+00:00
-- url     : https://prove2.me/theorems/1f9c4437-56cb-4871-8503-4793ccb71774
-- title:
--   P2 M PIW Adel Class Fin hform add right  73a64fb2bbe8: P2 M PIW Adel Class Fin hform add right  73a64fb2bbe8
-- statement:
--   The P2 M PIW Adel Class Fin hform add right  73a64fb2bbe8 construction uses the P2 M PIW Adel Class Fin hform add right  73a64fb2bbe8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L20-L22

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

theorem P2M_PIW_AdelClassFin_hform_add_right__73a64fb2bbe8 (x y y' : Fin m → E) :
    hform (starRingEnd E) J x (y + y') = hform (starRingEnd E) J x y + hform (starRingEnd E) J x y' := by sorry

alias «PIW».«AdelClassFin».«hform_add_right'» := P2M_PIW_AdelClassFin_hform_add_right__73a64fb2bbe8
