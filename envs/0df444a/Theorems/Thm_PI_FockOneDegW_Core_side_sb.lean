-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_side_sb
-- name    : PI.FockOneDegW.Core.side_sb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:50.499522+00:00
-- url     : https://prove2.me/theorems/3f74c59c-c001-4178-9a2e-51b29ceea4ff
-- title:
--   Core: side sb
-- statement:
--   The Core construction uses the side sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L64-L65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
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
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}

theorem PI.FockOneDegW.Core.side_sb {m n : ℕ} (a b : Ix m n) : sameBlock a b ↔ a.isLeft = b.isLeft := by sorry
