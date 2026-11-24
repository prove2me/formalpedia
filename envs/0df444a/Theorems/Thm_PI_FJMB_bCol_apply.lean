-- Prove2me | Theorems.Thm_PI_FJMB_bCol_apply
-- name    : PI.FJMB.bCol_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:12.734869+00:00
-- url     : https://prove2.me/theorems/929d2978-fbac-4a28-82e2-f7135442517d
-- title:
--   FJMB: b Col apply
-- statement:
--   The FJMB construction uses the b Col apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L16-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {σ : Type*}

theorem PI.FJMB.bCol_apply {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by sorry
