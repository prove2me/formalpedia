-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_Sd_af_algebraMap_apply
-- name    : PI.OmFibreUniq.W.Sd.af_algebraMap_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:27.171331+00:00
-- url     : https://prove2.me/theorems/0e5ae2a9-1310-5086-9536-c8350d990344
-- title:
--   Sd: af algebra Map apply
-- statement:
--   The Sd construction uses the af algebra Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/AdditiveCharacterNontrivial.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/AdditiveCharacterNontrivial.lean#L108-L109

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_AdditiveCharacterNontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology
open scoped TensorProduct

theorem PI.OmFibreUniq.W.Sd.af_algebraMap_apply {F : Type} [Field F] [NumberField F] (r : F) (w : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) r) w = algebraMap F (Fv F w) r := by sorry
