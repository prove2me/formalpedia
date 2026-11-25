-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_Coch_sum_sum_prod
-- name    : PositivityTheory.Rg.Cz.Coch.sum_sum_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:28.267942+00:00
-- url     : https://prove2.me/theorems/c649058d-298e-41eb-a3cc-8ce951778b46
-- title:
--   Coch: sum sum prod
-- statement:
--   The Coch construction uses the sum sum prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L53-L57

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

theorem PositivityTheory.Rg.Cz.Coch.sum_sum_prod {N : ℕ} {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R] (g : Fin N → α → β → R) :
    ∑ A : Fin N → α, ∑ B : Fin N → β, ∏ k, g k (A k) (B k) = ∏ k, ∑ a, ∑ b, g k a b := by sorry
