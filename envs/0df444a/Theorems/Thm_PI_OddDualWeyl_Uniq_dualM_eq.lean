-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Uniq_dualM_eq
-- name    : PI.OddDualWeyl.Uniq.dualM_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:52.38487+00:00
-- url     : https://prove2.me/theorems/69192310-8d19-43ed-a19b-64643afe2b0b
-- title:
--   Uniq: dual M eq
-- statement:
--   The Uniq construction uses the dual M eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L33-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Uniq
variable {Rg : Type*} [CommRing Rg] {k : ℕ}

theorem PI.OddDualWeyl.Uniq.dualM_eq : dualM Rg k = (adjugate (genM Rg k))ᵀ * P _ k := by sorry
