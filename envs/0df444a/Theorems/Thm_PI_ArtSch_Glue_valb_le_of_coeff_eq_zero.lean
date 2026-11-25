-- Prove2me | Theorems.Thm_PI_ArtSch_Glue_valb_le_of_coeff_eq_zero
-- name    : PI.ArtSch.Glue.valb_le_of_coeff_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:34.902297+00:00
-- url     : https://prove2.me/theorems/013e67aa-980c-5995-8ef8-7e0e86193a10
-- title:
--   Glue: valb le of coeff eq zero
-- statement:
--   The Glue construction uses the valb le of coeff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L27-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationGluing/ValbLeOfCoeffEqZero.lean#L27-L51

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

theorem PI.ArtSch.Glue.valb_le_of_coeff_eq_zero (r : OCb l) (n : ℕ) (hr : PreTilt.coeff n r = 0) :
    valb l r ≤ (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) ^ (l ^ n) := by sorry
