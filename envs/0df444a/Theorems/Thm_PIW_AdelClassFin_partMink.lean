-- Prove2me | Theorems.Thm_PIW_AdelClassFin_partMink
-- name    : PIW.AdelClassFin.partMink
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:21.078456+00:00
-- url     : https://prove2.me/theorems/2491428d-9308-48c7-a87e-61b5b3df4d62
-- title:
--   Adel Class Fin: part Mink
-- statement:
--   The Adel Class Fin construction uses the part Mink property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HmkFactor.lean#L101-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HmkFactor.lean#L101-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor
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
open MeasureTheory Matrix Module
open scoped MatrixOrder

theorem PIW.AdelClassFin.partMink : PartMink := by sorry
