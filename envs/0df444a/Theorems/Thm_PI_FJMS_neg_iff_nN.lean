-- Prove2me | Theorems.Thm_PI_FJMS_neg_iff_nN
-- name    : PI.FJMS.neg_iff_nN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:35.259112+00:00
-- url     : https://prove2.me/theorems/1df68b5d-ce4d-4d65-b9ee-16e525b5941f
-- title:
--   FJMS: neg iff n N
-- statement:
--   The FJMS construction uses the neg iff n N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L18-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L18-L50

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP

theorem PI.FJMS.neg_iff_nN {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) : f i < 0 ↔ n ≤ i.val + nN f := by sorry
