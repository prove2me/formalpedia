-- Prove2me | Theorems.Thm_PI_GreenHCLabel_basics_mono_of_inj
-- name    : PI.GreenHCLabel.basics_mono_of_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:55.400677+00:00
-- url     : https://prove2.me/theorems/a1306328-8e74-4d72-865d-ec6b87ef7464
-- title:
--   Green HCLabel: basics mono of inj
-- statement:
--   The Green HCLabel construction uses the basics mono of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/Basics.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/Basics.lean#L56-L60

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
noncomputable section
open PI PI.GreenHCLabel
variable {Γ : Type} [Group Γ]

theorem PI.GreenHCLabel.basics_mono_of_inj {σ τ : FDRep ℂ Γ} (f : σ ⟶ τ) (hf : Function.Injective (basicsLin f)) :
    Mono f := by sorry
