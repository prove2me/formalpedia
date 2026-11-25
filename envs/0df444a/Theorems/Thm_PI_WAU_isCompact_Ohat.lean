-- Prove2me | Theorems.Thm_PI_WAU_isCompact_Ohat
-- name    : PI.WAU.isCompact_Ohat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:16.769905+00:00
-- url     : https://prove2.me/theorems/097b0cc6-8bcd-4791-ba04-98005bdc1d2a
-- title:
--   WAU: is Compact Ohat
-- statement:
--   The WAU construction uses the is Compact Ohat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CartierFrobeniusFormLocal.lean#L110-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CartierFrobeniusFormLocal.lean#L110-L123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology
variable {F : Type} [Field F] [NumberField F]

theorem PI.WAU.isCompact_Ohat : IsCompact (Ohat F) := by sorry
