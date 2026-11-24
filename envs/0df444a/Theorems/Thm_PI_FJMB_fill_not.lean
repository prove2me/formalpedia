-- Prove2me | Theorems.Thm_PI_FJMB_fill_not
-- name    : PI.FJMB.fill_not
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:16.858454+00:00
-- url     : https://prove2.me/theorems/4ad5c3f0-2fcf-4905-b196-d54f65756ade
-- title:
--   FJMB: fill not
-- statement:
--   The FJMB construction uses the fill not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L52-L54

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

theorem PI.FJMB.fill_not {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K)
    (p : σ → K) (v : σ) (hv : ∀ x, ι x ≠ v) : fill ι M p v = p v := by sorry
