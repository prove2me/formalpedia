-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_B3_IotaPl_mem_smallIdeal
-- name    : ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:28.392618+00:00
-- url     : https://prove2.me/theorems/6a5cdefd-de01-4d36-8c91-390bced6786f
-- title:
--   Iota Pl: mem small Ideal
-- statement:
--   The Iota Pl construction uses the mem small Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlace.lean#L74-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlace.lean#L74-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.B3 ReciprocityTheory.ChartRestriction.B3.IotaPl
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := by sorry
