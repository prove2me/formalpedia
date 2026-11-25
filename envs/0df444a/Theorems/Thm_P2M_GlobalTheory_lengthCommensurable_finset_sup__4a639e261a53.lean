-- Prove2me | Theorems.Thm_P2M_GlobalTheory_lengthCommensurable_finset_sup__4a639e261a53
-- name    : P2M_GlobalTheory_lengthCommensurable_finset_sup__4a639e261a53
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:17.227599+00:00
-- url     : https://prove2.me/theorems/e5c35985-e107-4ee4-9740-e87c7685c299
-- title:
--   P2 M Global Theory length Commensurable finset sup  4a639e261a53: P2 M Global Theory length Commensurable finset sup  4a639e261a53
-- statement:
--   The P2 M Global Theory length Commensurable finset sup  4a639e261a53 construction uses the P2 M Global Theory length Commensurable finset sup  4a639e261a53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L204-L207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {A A' B B' C : Submodule R V}

theorem P2M_GlobalTheory_lengthCommensurable_finset_sup__4a639e261a53 {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → Submodule R V} (h : ∀ i ∈ s, LengthCommensurable A (f i)) :
    LengthCommensurable A (s.sup' hs f) := by sorry

alias «GlobalTheory».«lengthCommensurable_finset_sup'» := P2M_GlobalTheory_lengthCommensurable_finset_sup__4a639e261a53
