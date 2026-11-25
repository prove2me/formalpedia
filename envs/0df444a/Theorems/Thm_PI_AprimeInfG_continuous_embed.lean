-- Prove2me | Theorems.Thm_PI_AprimeInfG_continuous_embed
-- name    : PI.AprimeInfG.continuous_embed
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:40.759582+00:00
-- url     : https://prove2.me/theorems/010ed555-1fef-53f7-8f3a-2ea79984d2da
-- title:
--   Aprime Inf G: continuous embed
-- statement:
--   The Aprime Inf G construction uses the continuous embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L86-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_BlockEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open scoped Matrix
variable {n k : ℕ} {S : Finset (Fin n)}

theorem PI.AprimeInfG.continuous_embed (e : Fin k ≃ S) : Continuous (emb0 e) := by sorry
