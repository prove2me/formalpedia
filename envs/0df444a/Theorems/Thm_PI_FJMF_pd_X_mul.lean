-- Prove2me | Theorems.Thm_PI_FJMF_pd_X_mul
-- name    : PI.FJMF.pd_X_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:17.03399+00:00
-- url     : https://prove2.me/theorems/1de45e8e-1418-4df0-bf3c-b4526ed2d029
-- title:
--   FJMF: pd X mul
-- statement:
--   The FJMF construction uses the pd X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L23-L26

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

theorem PI.FJMF.pd_X_mul [DecidableEq σ] (l v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv l (X v * Q) = X v * pderiv l Q + (if v = l then Q else 0) := by sorry
