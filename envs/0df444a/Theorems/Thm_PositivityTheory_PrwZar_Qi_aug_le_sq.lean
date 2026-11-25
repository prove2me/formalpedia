-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_Qi_aug_le_sq
-- name    : PositivityTheory.PrwZar.Qi.aug_le_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:04.715383+00:00
-- url     : https://prove2.me/theorems/05b4d806-1772-4762-b369-2aa39a8026f4
-- title:
--   Qi: aug le sq
-- statement:
--   The Qi construction uses the aug le sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiCartier.lean#L63-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiCartier.lean#L63-L162

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCartier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem PositivityTheory.PrwZar.Qi.aug_le_sq {K H : Type} [Field K] [CharZero K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) :
    RingHom.ker ε ≤ RingHom.ker ε ^ 2 := by sorry
