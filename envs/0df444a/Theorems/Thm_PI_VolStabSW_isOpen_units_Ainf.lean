-- Prove2me | Theorems.Thm_PI_VolStabSW_isOpen_units_Ainf
-- name    : PI.VolStabSW.isOpen_units_Ainf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:46.463549+00:00
-- url     : https://prove2.me/theorems/34b0d538-5a02-474f-939a-761768932700
-- title:
--   Vol Stab SW: is Open units Ainf
-- statement:
--   The Vol Stab SW construction uses the is Open units Ainf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TensTop.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TensTop.lean#L200-L206

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolStabSW.isOpen_units_Ainf : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by sorry
