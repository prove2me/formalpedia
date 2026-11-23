-- Prove2me | Theorems.Thm_PI_VolStabW_isOpen_units_Ainf
-- name    : PI.VolStabW.isOpen_units_Ainf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:30.608143+00:00
-- url     : https://prove2.me/theorems/6abecd2c-2a49-4ab7-a1c1-7451289573a0
-- title:
--   Vol Stab W: is Open units Ainf
-- statement:
--   The Vol Stab W construction uses the is Open units Ainf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensTop.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensTop.lean#L206-L215

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolStabW.isOpen_units_Ainf : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by sorry
