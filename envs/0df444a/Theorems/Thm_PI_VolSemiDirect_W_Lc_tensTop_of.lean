-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Lc_tensTop_of
-- name    : PI.VolSemiDirect.W.Lc.tensTop_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:11.691749+00:00
-- url     : https://prove2.me/theorems/c6b366d3-0f46-4cb5-8336-66e72a6d174a
-- title:
--   Lc: tens Top of
-- statement:
--   The Lc construction uses the tens Top of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TensTopOf.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TensTopOf.lean#L31-L48

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

theorem PI.VolSemiDirect.W.Lc.tensTop_of (h : AFTop) : TensTop := by sorry
