-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Lc_finite_nf
-- name    : PI.VolSemiDirect.W.Lc.finite_nf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:01.97889+00:00
-- url     : https://prove2.me/theorems/a19498a3-8760-4d34-98a8-0aaee2487cad
-- title:
--   Lc: finite nf
-- statement:
--   The Lc construction uses the finite nf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TensTopOf.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TensTopOf.lean#L16-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TensTopOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Lc
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem PI.VolSemiDirect.W.Lc.finite_nf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Module.Finite F E := by sorry
