-- Prove2me | Theorems.Thm_P2M_PI_FJMB_fill___d91e4e7a1ca5
-- name    : P2M_PI_FJMB_fill___d91e4e7a1ca5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:32.508717+00:00
-- url     : https://prove2.me/theorems/96682521-3875-483b-b53f-03b13dd90f61
-- title:
--   P2 M PI FJMB fill   d91e4e7a1ca5: P2 M PI FJMB fill   d91e4e7a1ca5
-- statement:
--   The P2 M PI FJMB fill   d91e4e7a1ca5 construction uses the P2 M PI FJMB fill   d91e4e7a1ca5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L48-L50

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

theorem P2M_PI_FJMB_fill___d91e4e7a1ca5 {K : Type*} {m n : ℕ} {ι : Fin m × Fin n → σ} (hι : Function.Injective ι) (M : Fin m → Fin n → K)
    (p : σ → K) (x : Fin m × Fin n) : fill ι M p (ι x) = M x.1 x.2 := by sorry

alias «PI».«FJMB».«fill_ι» := P2M_PI_FJMB_fill___d91e4e7a1ca5
