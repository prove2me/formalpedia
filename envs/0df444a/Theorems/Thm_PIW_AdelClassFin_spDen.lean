-- Prove2me | Theorems.Thm_PIW_AdelClassFin_spDen
-- name    : PIW.AdelClassFin.spDen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:36.213798+00:00
-- url     : https://prove2.me/theorems/6d182e63-de36-54e2-bf89-2250881245bf
-- title:
--   Adel Class Fin: sp Den
-- statement:
--   The Adel Class Fin construction uses the sp Den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SpDen.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SpDen.lean#L10-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SpDen
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
open NumberField

theorem PIW.AdelClassFin.spDen : SpDen := by sorry
