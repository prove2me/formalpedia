-- Prove2me | Theorems.Thm_P2M_PI_VolStabW_SdTestInfW_pairHerm_add_right__b5dc66635d8a
-- name    : P2M_PI_VolStabW_SdTestInfW_pairHerm_add_right__b5dc66635d8a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:40.856703+00:00
-- url     : https://prove2.me/theorems/0e900b65-3645-403a-ae11-ebfe60441d93
-- title:
--   P2 M PI Vol Stab W Sd Test Inf W pair Herm add right  b5dc66635d8a: P2 M PI Vol Stab W Sd Test Inf W pair Herm add right  b5dc66635d8a
-- statement:
--   The P2 M PI Vol Stab W Sd Test Inf W pair Herm add right  b5dc66635d8a construction uses the P2 M PI Vol Stab W Sd Test Inf W pair Herm add right  b5dc66635d8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L261-L264

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem P2M_PI_VolStabW_SdTestInfW_pairHerm_add_right__b5dc66635d8a (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n S (T + U) = pairHerm R σ n S T + pairHerm R σ n S U := by sorry

alias «PI».«VolStabW».«SdTestInfW».«pairHerm_add_right'» := P2M_PI_VolStabW_SdTestInfW_pairHerm_add_right__b5dc66635d8a
