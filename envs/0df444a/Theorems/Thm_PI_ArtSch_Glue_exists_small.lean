-- Prove2me | Theorems.Thm_PI_ArtSch_Glue_exists_small
-- name    : PI.ArtSch.Glue.exists_small
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:28.758073+00:00
-- url     : https://prove2.me/theorems/d1f463c5-e593-508e-9987-6df89a72cc91
-- title:
--   Glue: exists small
-- statement:
--   The Glue construction uses the exists small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L53-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]

theorem PI.ArtSch.Glue.exists_small (t : ℝ≥0) (ht : 0 < t) :
    ∃ n : ℕ, (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) ^ (l ^ n) < t := by sorry
