-- Prove2me | Theorems.Thm_P2M_Formalism_REAL_sum_sum_sum_sum_comm__604324486430
-- name    : P2M_Formalism_REAL_sum_sum_sum_sum_comm__604324486430
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:05.093086+00:00
-- url     : https://prove2.me/theorems/45bd292f-6542-4cc2-8158-abb929cbc106
-- title:
--   P2 M Formalism REAL sum sum sum sum comm  604324486430: P2 M Formalism REAL sum sum sum sum comm  604324486430
-- statement:
--   The P2 M Formalism REAL sum sum sum sum comm  604324486430 construction uses the P2 M Formalism REAL sum sum sum sum comm  604324486430 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L207-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L207-L217

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {A : Type*} [Ring A] {m n : ℕ} (B P : Fin m → Fin n → A)
variable {B P}
variable (hBP : ∀ i j a b, B i a * P j b - P j b * B i a = if i = j ∧ a = b then 1 else 0)
  (hBB : ∀ i j a b, B i a * B j b = B j b * B i a)
  (hPP : ∀ i j a b, P i a * P j b = P j b * P i a)
include hBP hBB hPP
omit hBP hBB hPP

theorem P2M_Formalism_REAL_sum_sum_sum_sum_comm__604324486430 {α β : Type*} [Fintype α] [Fintype β] (f : α → α → β → β → A) :
    ∑ x, ∑ y, ∑ i, ∑ j, f i j x y = ∑ i, ∑ j, ∑ x, ∑ y, f i j x y := by sorry

alias «Formalism».«REAL».«sum_sum_sum_sum_comm'» := P2M_Formalism_REAL_sum_sum_sum_sum_comm__604324486430
