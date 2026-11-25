-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HCdecomp_Red_mul___00b8b2883c0d
-- name    : P2M_GlobalTheory_CompanionTheory_HCdecomp_Red_mul___00b8b2883c0d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:01.313362+00:00
-- url     : https://prove2.me/theorems/b8879f1c-c4fc-4921-b61e-bca78602d07f
-- title:
--   P2 M Global Theory Companion Theory HCdecomp Red mul   00b8b2883c0d: P2 M Global Theory Companion Theory HCdecomp Red mul   00b8b2883c0d
-- statement:
--   The P2 M Global Theory Companion Theory HCdecomp Red mul   00b8b2883c0d construction uses the P2 M Global Theory Companion Theory HCdecomp Red mul   00b8b2883c0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L265-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L265-L273

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

theorem P2M_GlobalTheory_CompanionTheory_HCdecomp_Red_mul___00b8b2883c0d {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (p : Fin n × Fin n) :
    Red (a * FreeAlgebra.ι ℂ p) := by sorry

alias «GlobalTheory».«CompanionTheory».«HCdecomp».«Red».«mul_ι» := P2M_GlobalTheory_CompanionTheory_HCdecomp_Red_mul___00b8b2883c0d
