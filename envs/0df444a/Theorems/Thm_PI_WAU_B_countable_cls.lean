-- Prove2me | Theorems.Thm_PI_WAU_B_countable_cls
-- name    : PI.WAU.B.countable_cls
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:43:30.346031+00:00
-- url     : https://prove2.me/theorems/6bc82145-f179-475e-8e0c-ae631ba2b07a
-- title:
--   B: countable cls
-- statement:
--   The B construction uses the countable cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L67-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]

theorem PI.WAU.B.countable_cls (M : ℕ) : Countable (Bad F M → F) := by sorry
