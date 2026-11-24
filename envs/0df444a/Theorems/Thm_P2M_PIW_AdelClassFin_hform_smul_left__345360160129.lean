-- Prove2me | Theorems.Thm_P2M_PIW_AdelClassFin_hform_smul_left__345360160129
-- name    : P2M_PIW_AdelClassFin_hform_smul_left__345360160129
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:28:13.762937+00:00
-- url     : https://prove2.me/theorems/7dfa28e2-d262-493f-af34-841e6d5fe0fd
-- title:
--   P2 M PIW Adel Class Fin hform smul left  345360160129: P2 M PIW Adel Class Fin hform smul left  345360160129
-- statement:
--   The P2 M PIW Adel Class Fin hform smul left  345360160129 construction uses the P2 M PIW Adel Class Fin hform smul left  345360160129 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L24-L32

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

theorem P2M_PIW_AdelClassFin_hform_smul_left__345360160129 (c : E) (x y : Fin m → E) :
    hform (starRingEnd E) J (c • x) y = star c * hform (starRingEnd E) J x y := by sorry

alias «PIW».«AdelClassFin».«hform_smul_left'» := P2M_PIW_AdelClassFin_hform_smul_left__345360160129
