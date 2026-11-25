-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_phGram_of
-- name    : PI.UnitaryGroupMassFormula.PhGram.phGram_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:03.413804+00:00
-- url     : https://prove2.me/theorems/66a72917-f560-4655-bab9-750c56db0abb
-- title:
--   Ph Gram: ph Gram of
-- statement:
--   The Ph Gram construction uses the ph Gram of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/PhGramOf.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/PhGramOf.lean#L12-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_PhGramOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram

theorem PI.UnitaryGroupMassFormula.PhGram.phGram_of (hC : Column) (hG : Gather) : PI.FglGram.PhGram := by sorry
