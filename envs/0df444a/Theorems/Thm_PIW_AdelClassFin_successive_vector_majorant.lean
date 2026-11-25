-- Prove2me | Theorems.Thm_PIW_AdelClassFin_successive_vector_majorant
-- name    : PIW.AdelClassFin.successive_vector_majorant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:36.419803+00:00
-- url     : https://prove2.me/theorems/d30d6081-cb1a-4a37-a671-9cf3fab0ca5f
-- title:
--   Adel Class Fin: successive vector majorant
-- statement:
--   The Adel Class Fin construction uses the successive vector majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorMajorantE.lean#L25-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorMajorantE.lean#L25-L65

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

theorem PIW.AdelClassFin.successive_vector_majorant : SvMaj := by sorry
