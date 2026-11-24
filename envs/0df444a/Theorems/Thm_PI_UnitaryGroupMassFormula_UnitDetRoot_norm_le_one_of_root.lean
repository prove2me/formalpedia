-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_norm_le_one_of_root
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.norm_le_one_of_root
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:00.496201+00:00
-- url     : https://prove2.me/theorems/57e96d3b-6b53-448c-b827-7f6fd5c50578
-- title:
--   Unit Det Root: norm le one of root
-- statement:
--   The Unit Det Root construction uses the norm le one of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NormLeOneOfRoot.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NormLeOneOfRoot.lean#L35-L37

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.norm_le_one_of_root {F : Type*} [NormedField F] [IsUltrametricDist F] {y : F}
    (p : Polynomial ℤ) (hp : p.Monic) (hpy : p.eval₂ (Int.castRingHom F) y = 0) : ‖y‖ ≤ 1 := by sorry
