-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Uniq_map_genM
-- name    : PI.OddDualWeyl.Uniq.map_genM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:07.571575+00:00
-- url     : https://prove2.me/theorems/12195bf2-6b41-4fb7-a32d-79a1e089ae6e
-- title:
--   Uniq: map gen M
-- statement:
--   The Uniq construction uses the map gen M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L36-L37

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

theorem PI.OddDualWeyl.Uniq.map_genM : (dualSub Rg k).toRingHom.mapMatrix (genM Rg k) = dualM Rg k := by sorry
