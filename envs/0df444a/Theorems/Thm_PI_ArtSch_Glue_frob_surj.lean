-- Prove2me | Theorems.Thm_PI_ArtSch_Glue_frob_surj
-- name    : PI.ArtSch.Glue.frob_surj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:26.829481+00:00
-- url     : https://prove2.me/theorems/0479f866-7f04-5b9c-9dbe-a51187b1e39f
-- title:
--   Glue: frob surj
-- statement:
--   The Glue construction uses the frob surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L60-L63

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

theorem PI.ArtSch.Glue.frob_surj (hR : RootModP) : Function.Surjective (frobenius (ModP (OC l) l) l) := by sorry
