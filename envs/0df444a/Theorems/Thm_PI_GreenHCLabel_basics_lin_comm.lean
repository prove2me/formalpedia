-- Prove2me | Theorems.Thm_PI_GreenHCLabel_basics_lin_comm
-- name    : PI.GreenHCLabel.basics_lin_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:31.775615+00:00
-- url     : https://prove2.me/theorems/be3eb06c-0c7e-4471-b2de-0d79c74b5cc6
-- title:
--   Green HCLabel: basics lin comm
-- statement:
--   The Green HCLabel construction uses the basics lin comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/Basics.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/Basics.lean#L16-L21

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

theorem PI.GreenHCLabel.basics_lin_comm {σ τ : FDRep ℂ Γ} (f : σ ⟶ τ) (g : Γ) :
    basicsLin f ∘ₗ σ.ρ g = τ.ρ g ∘ₗ basicsLin f := by sorry
