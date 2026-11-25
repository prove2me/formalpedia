-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_isOpen_nbhdA
-- name    : PI.VolSemiDirect.W.isOpen_nbhdA
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:37:28.978815+00:00
-- url     : https://prove2.me/theorems/15376c3d-c550-4cc3-90a5-434f51908b4e
-- title:
--   W: is Open nbhd A
-- statement:
--   The W construction uses the is Open nbhd A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/EqZeroOfMemNbhdA.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/EqZeroOfMemNbhdA.lean#L23-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolSemiDirect.W.isOpen_nbhdA : IsOpen (nbhdA F) := by sorry
