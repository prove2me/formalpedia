-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svM_term
-- name    : PIW.AdelClassFin.svM_term
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:26.821557+00:00
-- url     : https://prove2.me/theorems/6d4d892c-c046-4b35-af98-ff4aea2e1113
-- title:
--   Adel Class Fin: sv M term
-- statement:
--   The Adel Class Fin construction uses the sv M term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorMajorantE.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorMajorantE.lean#L21-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorMajorantE
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
open Formalism.UG NumberField Matrix
open scoped ComplexOrder

theorem PIW.AdelClassFin.svM_term (r : ℝ) (w : ℂ) : star w * ((r : ℂ) * w) = ((r * ‖w‖ ^ 2 : ℝ) : ℂ) := by sorry
