-- Prove2me | Theorems.Thm_PI_AprimeInfG_restrict_embed
-- name    : PI.AprimeInfG.restrict_embed
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:05.214389+00:00
-- url     : https://prove2.me/theorems/7eb260e9-e151-48ec-a03c-662d52cac849
-- title:
--   Aprime Inf G: restrict embed
-- statement:
--   The Aprime Inf G construction uses the restrict embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L117-L119

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

theorem PI.AprimeInfG.restrict_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : resB e (emb0 e X) = X := by sorry
