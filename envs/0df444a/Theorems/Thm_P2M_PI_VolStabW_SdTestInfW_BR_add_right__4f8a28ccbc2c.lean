-- Prove2me | Theorems.Thm_P2M_PI_VolStabW_SdTestInfW_BR_add_right__4f8a28ccbc2c
-- name    : P2M_PI_VolStabW_SdTestInfW_BR_add_right__4f8a28ccbc2c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:07.479979+00:00
-- url     : https://prove2.me/theorems/2bcc54c1-9c02-4b6c-b291-411ea7fa45fa
-- title:
--   P2 M PI Vol Stab W Sd Test Inf W BR add right  4f8a28ccbc2c: P2 M PI Vol Stab W Sd Test Inf W BR add right  4f8a28ccbc2c
-- statement:
--   The P2 M PI Vol Stab W Sd Test Inf W BR add right  4f8a28ccbc2c construction uses the P2 M PI Vol Stab W Sd Test Inf W BR add right  4f8a28ccbc2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L257-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L257-L259

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

theorem P2M_PI_VolStabW_SdTestInfW_BR_add_right__4f8a28ccbc2c (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → R ⊗[F] E) : BR R σ J X (Y + Y') = BR R σ J X Y + BR R σ J X Y' := by sorry

alias «PI».«VolStabW».«SdTestInfW».«BR_add_right'» := P2M_PI_VolStabW_SdTestInfW_BR_add_right__4f8a28ccbc2c
