-- Prove2me | Theorems.Thm_PI_AprimeInfG_sum_norm_sq_embed
-- name    : PI.AprimeInfG.sum_norm_sq_embed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:59.110306+00:00
-- url     : https://prove2.me/theorems/5f4379f2-3a4a-4811-85d2-b8853d5032a0
-- title:
--   Aprime Inf G: sum norm sq embed
-- statement:
--   The Aprime Inf G construction uses the sum norm sq embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L145-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BlockEmb.lean#L145-L154

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

theorem PI.AprimeInfG.sum_norm_sq_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖emb0 e X i j‖ ^ 2) = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by sorry
