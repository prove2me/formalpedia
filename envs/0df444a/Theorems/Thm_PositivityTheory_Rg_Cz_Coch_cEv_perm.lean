-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_Coch_cEv_perm
-- name    : PositivityTheory.Rg.Cz.Coch.cEv_perm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:10.865566+00:00
-- url     : https://prove2.me/theorems/642d84ec-629b-437f-a86e-ee8904dd678e
-- title:
--   Coch: c Ev perm
-- statement:
--   The Coch construction uses the c Ev perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L25-L32

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.Coch
variable {H V : Type*} [AddCommGroup V] [Module ℂ V]

theorem PositivityTheory.Rg.Cz.Coch.cEv_perm {N : ℕ} (F : (Fin N → H) → V) (σ : Equiv.Perm (Fin N)) (A B : Fin N → H) :
    cEv (fun v => F (fun i => v (σ i))) A B = cEv F (fun i => A (σ i)) (fun i => B (σ i)) := by sorry
