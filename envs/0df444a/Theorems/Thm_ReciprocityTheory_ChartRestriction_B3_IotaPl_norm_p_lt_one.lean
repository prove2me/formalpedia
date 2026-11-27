-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_B3_IotaPl_norm_p_lt_one
-- name    : ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:56.936264+00:00
-- url     : https://prove2.me/theorems/34fbe26d-c85d-4635-8bf4-0d1cab1f4f05
-- title:
--   Iota Pl: norm p lt one
-- statement:
--   The Iota Pl construction uses the norm p lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlace.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlace.lean#L92-L101

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

theorem ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by sorry
