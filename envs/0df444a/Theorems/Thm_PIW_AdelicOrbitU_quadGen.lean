-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_quadGen
-- name    : PIW.AdelicOrbitU.quadGen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:49.421021+00:00
-- url     : https://prove2.me/theorems/e7fcc7b0-2c0b-4c3a-95a8-9b0e1d84325a
-- title:
--   Adelic Orbit U: quad Gen
-- statement:
--   The Adelic Orbit U construction uses the quad Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/StLamOf.lean#L201-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/StLamOf.lean#L201-L265

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU

theorem PIW.AdelicOrbitU.quadGen : QuadGen := by sorry
