-- Prove2me | Theorems.Thm_PI_GreenHCLabel_basics_lin_comp
-- name    : PI.GreenHCLabel.basics_lin_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:02.785273+00:00
-- url     : https://prove2.me/theorems/62585216-5f57-5d1e-ae62-f41c7cf29f08
-- title:
--   Green HCLabel: basics lin comp
-- statement:
--   The Green HCLabel construction uses the basics lin comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/Basics.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/Basics.lean#L23-L24

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

theorem PI.GreenHCLabel.basics_lin_comp {σ τ υ : FDRep ℂ Γ} (f : σ ⟶ τ) (h : τ ⟶ υ) :
    basicsLin (f ≫ h) = basicsLin h ∘ₗ basicsLin f := by sorry
