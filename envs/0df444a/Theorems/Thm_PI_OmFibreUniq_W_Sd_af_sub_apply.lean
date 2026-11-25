-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_Sd_af_sub_apply
-- name    : PI.OmFibreUniq.W.Sd.af_sub_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:17:55.741658+00:00
-- url     : https://prove2.me/theorems/5047f9da-7bb1-52db-88ce-5f94fcfc60d4
-- title:
--   Sd: af sub apply
-- statement:
--   The Sd construction uses the af sub apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/AdditiveCharacterNontrivial.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/AdditiveCharacterNontrivial.lean#L95-L96

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

theorem PI.OmFibreUniq.W.Sd.af_sub_apply {F : Type} [Field F] [NumberField F] (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (a - b) w = a w - b w := by sorry
