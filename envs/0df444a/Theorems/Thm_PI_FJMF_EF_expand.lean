-- Prove2me | Theorems.Thm_PI_FJMF_EF_expand
-- name    : PI.FJMF.EF_expand
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:20.270836+00:00
-- url     : https://prove2.me/theorems/e5072d16-986a-4a01-804d-eb5e6cdbab52
-- title:
--   FJMF: EF expand
-- statement:
--   The FJMF construction uses the EF expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L32-L38

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

theorem PI.FJMF.EF_expand (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) =
      (∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P))) +
        ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P := by sorry
