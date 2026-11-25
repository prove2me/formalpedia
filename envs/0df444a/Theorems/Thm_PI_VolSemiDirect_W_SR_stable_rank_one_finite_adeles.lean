-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_SR_stable_rank_one_finite_adeles
-- name    : PI.VolSemiDirect.W.SR.stable_rank_one_finite_adeles
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:27.454808+00:00
-- url     : https://prove2.me/theorems/327a222e-60db-4941-9690-7d1b5aa1509b
-- title:
--   SR: stable rank one finite adeles
-- statement:
--   The SR construction uses the stable rank one finite adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HasStableRangeOne.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HasStableRangeOne.lean#L101-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HasStableRangeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.SR
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped RestrictedProduct

theorem PI.VolSemiDirect.W.SR.stable_rank_one_finite_adeles (F : Type) [Field F] [NumberField F] :
    Cj.HasStableRangeOne (FiniteAdeleRing (𝓞 F) F) := by sorry
