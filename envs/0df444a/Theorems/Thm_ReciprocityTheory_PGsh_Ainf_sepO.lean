-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_sepO
-- name    : ReciprocityTheory.PGsh.Ainf.sepO
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:45.168714+00:00
-- url     : https://prove2.me/theorems/219ea1f9-a066-4565-886c-a0e397d22880
-- title:
--   Ainf: sep O
-- statement:
--   The Ainf construction uses the sep O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L77-L83

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem ReciprocityTheory.PGsh.Ainf.sepO (a : O) (h : ∀ n : ℕ, a ∈ span {(p : O) ^ (n + 1)}) : a = 0 := by sorry
