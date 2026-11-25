-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_frob_surj
-- name    : ReciprocityTheory.PGsh.Ainf.frob_surj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:05.546127+00:00
-- url     : https://prove2.me/theorems/976c5547-bb97-4368-8b31-d6b03bce3982
-- title:
--   Ainf: frob surj
-- statement:
--   The Ainf construction uses the frob surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L41-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L41-L54

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

theorem ReciprocityTheory.PGsh.Ainf.frob_surj (hv : v.Integers O) : Function.Surjective (frobenius (ModP O p) p) := by sorry
