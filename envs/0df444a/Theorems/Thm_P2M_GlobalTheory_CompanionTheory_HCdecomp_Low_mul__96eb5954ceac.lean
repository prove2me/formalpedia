-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HCdecomp_Low_mul__96eb5954ceac
-- name    : P2M_GlobalTheory_CompanionTheory_HCdecomp_Low_mul__96eb5954ceac
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:32.99401+00:00
-- url     : https://prove2.me/theorems/faba42b1-328c-46b4-9c30-f912a3c325f4
-- title:
--   P2 M Global Theory Companion Theory HCdecomp Low mul  96eb5954ceac: P2 M Global Theory Companion Theory HCdecomp Low mul  96eb5954ceac
-- statement:
--   The P2 M Global Theory Companion Theory HCdecomp Low mul  96eb5954ceac construction uses the P2 M Global Theory Companion Theory HCdecomp Low mul  96eb5954ceac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L159-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L159-L202

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}

theorem P2M_GlobalTheory_CompanionTheory_HCdecomp_Low_mul__96eb5954ceac {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∃ b : FreeAlgebra ℂ (Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E u - evd (fun c => E c c) b ∈ PP E := by sorry

alias «GlobalTheory».«CompanionTheory».«HCdecomp».«Low».«mul'» := P2M_GlobalTheory_CompanionTheory_HCdecomp_Low_mul__96eb5954ceac
