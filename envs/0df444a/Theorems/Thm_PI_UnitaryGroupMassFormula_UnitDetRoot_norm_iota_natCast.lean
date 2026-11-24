-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_norm_iota_natCast
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.norm_iota_natCast
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:48.06757+00:00
-- url     : https://prove2.me/theorems/d430a71a-5181-4bb1-92c7-839df462bc16
-- title:
--   Unit Det Root: norm iota nat Cast
-- statement:
--   The Unit Det Root construction uses the norm iota nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NormLeOneOfRoot.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NormLeOneOfRoot.lean#L39-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.norm_iota_natCast (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (k : ℕ) (hk : ¬ l ∣ k) :
    ‖ι (k : ℂ)‖ = 1 := by sorry
