-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_Sd_exists_pi
-- name    : PI.OmFibreUniq.W.Sd.exists_pi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:17:03.826485+00:00
-- url     : https://prove2.me/theorems/30641335-cb56-57be-b804-80accf4457fe
-- title:
--   Sd: exists pi
-- statement:
--   The Sd construction uses the exists pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/AdditiveCharacterNontrivial.lean#L45-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/AdditiveCharacterNontrivial.lean#L45-L68

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

theorem PI.OmFibreUniq.W.Sd.exists_pi (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, π ∈ v.asIdeal ∧ π ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → π ∉ w.asIdeal := by sorry
