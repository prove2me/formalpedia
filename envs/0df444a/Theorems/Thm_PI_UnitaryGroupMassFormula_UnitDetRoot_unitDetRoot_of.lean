-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_unitDetRoot_of
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:11.569041+00:00
-- url     : https://prove2.me/theorems/029afa8c-cfb0-4558-b63e-7a45090395c8
-- title:
--   Unit Det Root: unit Det Root of
-- statement:
--   The Unit Det Root construction uses the unit Det Root of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/UnitDetRootOf.lean#L10-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/UnitDetRootOf.lean#L10-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_UnitDetRootOf
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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of (h1 : DetInK) (h2 : LocalStd) (h3 : GlobalLUnit) (h4 : NormOne)
    (h5 : RootStep) (h6 : ConjMem) (h7 : ConjLUnit) : PI.UnitDetRoot := by sorry
