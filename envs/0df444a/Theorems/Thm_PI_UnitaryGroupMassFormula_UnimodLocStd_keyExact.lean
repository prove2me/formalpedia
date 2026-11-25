-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_keyExact
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.keyExact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:55.883251+00:00
-- url     : https://prove2.me/theorems/0f602f35-9c81-5bd6-96b0-1d57f799bfb2
-- title:
--   Unimod Loc Std: key Exact
-- statement:
--   The Unimod Loc Std construction uses the key Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/KeyExact.lean#L95-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/KeyExact.lean#L95-L255

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.keyExact : KeyExact := by sorry
