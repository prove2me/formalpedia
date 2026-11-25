-- Prove2me | Theorems.Thm_P2M_PI_VolStabW_SdTestInfW_continuous_psiInf__007137ef755b
-- name    : P2M_PI_VolStabW_SdTestInfW_continuous_psiInf__007137ef755b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:10.22591+00:00
-- url     : https://prove2.me/theorems/21cf3b4a-201b-5af8-b5cc-795f97d76d4b
-- title:
--   P2 M PI Vol Stab W Sd Test Inf W continuous psi Inf  007137ef755b: P2 M PI Vol Stab W Sd Test Inf W continuous psi Inf  007137ef755b
-- statement:
--   The P2 M PI Vol Stab W Sd Test Inf W continuous psi Inf  007137ef755b construction uses the P2 M PI Vol Stab W Sd Test Inf W continuous psi Inf  007137ef755b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L298-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L298-L302

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

theorem P2M_PI_VolStabW_SdTestInfW_continuous_psiInf__007137ef755b {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) : Continuous (psiInf F ψ) := by sorry

alias «PI».«VolStabW».«SdTestInfW».«continuous_psiInf'» := P2M_PI_VolStabW_SdTestInfW_continuous_psiInf__007137ef755b
