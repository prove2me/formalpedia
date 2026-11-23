-- Prove2me | Theorems.Thm_PI_VolStabS_isOpen_units_Ainf
-- name    : PI.VolStabS.isOpen_units_Ainf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:12.633329+00:00
-- url     : https://prove2.me/theorems/4d3650d8-c22b-4b94-962f-ed7e289b3ad6
-- title:
--   Vol Stab S: is Open units Ainf
-- statement:
--   The Vol Stab S construction uses the is Open units Ainf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/TensTop.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/TensTop.lean#L201-L208

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolStabS.isOpen_units_Ainf : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by sorry
