-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_transvection_preserves_haar
-- name    : PI.VolSemiDirect.W.Cj.transvection_preserves_haar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:42.458552+00:00
-- url     : https://prove2.me/theorems/4f54d00f-9918-5d5b-bce7-29a14e922c1b
-- title:
--   Cj: transvection preserves haar
-- statement:
--   The Cj construction uses the transvection preserves haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/UniHaar.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/UniHaar.lean#L116-L119

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_UniHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open MeasureTheory

theorem PI.VolSemiDirect.W.Cj.transvection_preserves_haar : TransvHaar := by sorry
