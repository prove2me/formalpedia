-- Prove2me | Theorems.Thm_PI_FJMF_comm_eq
-- name    : PI.FJMF.comm_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:20.712145+00:00
-- url     : https://prove2.me/theorems/b8cd1f07-a321-4d48-9023-9f7b2b46f53b
-- title:
--   FJMF: comm eq
-- statement:
--   The FJMF construction uses the comm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L54-L66

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

theorem PI.FJMF.comm_eq (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) - PI.FJM.bRow ι b a (PI.FJM.bRow ι a b P) =
      ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P - ∑ k : Fin n, X (ι (b, k)) * pderiv (ι (b, k)) P := by sorry
