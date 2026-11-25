-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_Coch_cEv_sum
-- name    : PositivityTheory.Rg.Cz.Coch.cEv_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:12.849592+00:00
-- url     : https://prove2.me/theorems/7b25fb78-8ed7-4be9-8aaf-bbd74f61bce0
-- title:
--   Coch: c Ev sum
-- statement:
--   The Coch construction uses the c Ev sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L17-L23

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

theorem PositivityTheory.Rg.Cz.Coch.cEv_sum {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℤ) (F : ι → (Fin N → H) → V) (A B : Fin N → H) :
    cEv (fun v => ∑ i ∈ s, c i • F i v) A B = ∑ i ∈ s, c i • cEv (F i) A B := by sorry
