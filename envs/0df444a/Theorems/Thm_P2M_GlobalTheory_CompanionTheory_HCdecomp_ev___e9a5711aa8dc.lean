-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HCdecomp_ev___e9a5711aa8dc
-- name    : P2M_GlobalTheory_CompanionTheory_HCdecomp_ev___e9a5711aa8dc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:54.908926+00:00
-- url     : https://prove2.me/theorems/e7e64123-cb94-4157-a837-95ccb857deed
-- title:
--   P2 M Global Theory Companion Theory HCdecomp ev   e9a5711aa8dc: P2 M Global Theory Companion Theory HCdecomp ev   e9a5711aa8dc
-- statement:
--   The P2 M Global Theory Companion Theory HCdecomp ev   e9a5711aa8dc construction uses the P2 M Global Theory Companion Theory HCdecomp ev   e9a5711aa8dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L144-L146

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem P2M_GlobalTheory_CompanionTheory_HCdecomp_ev___e9a5711aa8dc (E : Fin n → Fin n → Module.End ℂ V) (p : Fin n × Fin n) :
    ev E (FreeAlgebra.ι ℂ p) = E p.1 p.2 := by sorry

alias «GlobalTheory».«CompanionTheory».«HCdecomp».«ev_ι» := P2M_GlobalTheory_CompanionTheory_HCdecomp_ev___e9a5711aa8dc
