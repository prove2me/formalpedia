-- Prove2me | Theorems.Thm_PI_VolStabSW_VolAAW_ev_int_all
-- name    : PI.VolStabSW.VolAAW.ev_int_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:59.259264+00:00
-- url     : https://prove2.me/theorems/22e3a00a-4f90-4ca5-bde0-e9ebe33b7a26
-- title:
--   Vol AAW: ev int all
-- statement:
--   The Vol AAW construction uses the ev int all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVolA.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVolA.lean#L98-L100

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabSW.VolAAW.ev_int_all {ι : Type} [Finite ι] (f : ι → F) :
    ∀ᶠ v in cofinite, ∀ i, algebraMap F (Fv F v) (f i) ∈ (v.adicCompletionIntegers F) := by sorry
