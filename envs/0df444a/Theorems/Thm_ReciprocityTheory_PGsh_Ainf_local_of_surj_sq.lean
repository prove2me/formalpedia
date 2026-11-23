-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_local_of_surj_sq
-- name    : ReciprocityTheory.PGsh.Ainf.local_of_surj_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:42.033498+00:00
-- url     : https://prove2.me/theorems/ce4e6774-b72c-4409-9f4e-b0882685be39
-- title:
--   Ainf: local of surj sq
-- statement:
--   The Ainf construction uses the local of surj sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L88-L103

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

theorem ReciprocityTheory.PGsh.Ainf.local_of_surj_sq {S T : Type} [CommRing S] [CommRing T] [IsLocalRing T] (f : S →+* T)
    (hf : Function.Surjective f) (hk : ∀ k ∈ RingHom.ker f, k * k = 0) : IsLocalRing S := by sorry
