-- Prove2me | Theorems.Thm_PI_FJMF_sum_ite_row
-- name    : PI.FJMF.sum_ite_row
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:45.852741+00:00
-- url     : https://prove2.me/theorems/1701cb5a-abb8-49e1-86ae-ed90bb9a1984
-- title:
--   FJMF: sum ite row
-- statement:
--   The FJMF construction uses the sum ite row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L28-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PI PI.FJMF
variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)

theorem PI.FJMF.sum_ite_row [DecidableEq σ] (hι : Function.Injective ι) (b : Fin m) (k : Fin n) (G : Fin n → MvPolynomial σ ℂ) :
    ∑ j : Fin n, (if ι (b, j) = ι (b, k) then G j else 0) = G k := by sorry
