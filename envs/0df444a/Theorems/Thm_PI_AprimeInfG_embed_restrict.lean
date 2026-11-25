-- Prove2me | Theorems.Thm_PI_AprimeInfG_embed_restrict
-- name    : PI.AprimeInfG.embed_restrict
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:12.25245+00:00
-- url     : https://prove2.me/theorems/7fb236d5-7caa-50f8-8499-df9f5450fcf9
-- title:
--   Aprime Inf G: embed restrict
-- statement:
--   The Aprime Inf G construction uses the embed restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L121-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L121-L131

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

theorem PI.AprimeInfG.embed_restrict (e : Fin k ≃ S) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) :
    emb0 e (resB e M) = M := by sorry
