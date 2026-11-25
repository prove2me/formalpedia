-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_d___apply_eq_sum_78c801493460
-- name    : P2M_GroundTheory_GroupCoh_d___apply_eq_sum_78c801493460
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:53.331742+00:00
-- url     : https://prove2.me/theorems/4f2624df-0ca8-4baf-b289-394fb879531e
-- title:
--   P2 M Ground Theory Group Coh d   apply eq sum 78c801493460: P2 M Ground Theory Group Coh d   apply eq sum 78c801493460
-- statement:
--   The P2 M Ground Theory Group Coh d   apply eq sum 78c801493460 construction uses the P2 M Ground Theory Group Coh d   apply eq sum 78c801493460 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L48-L52

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}

theorem P2M_GroundTheory_GroupCoh_d___apply_eq_sum_78c801493460 (z : G →₀ A) :
    d₁₀ A z = ∑ g ∈ z.support, (A.ρ g⁻¹ (z g) - z g) := by sorry

alias «GroundTheory».«GroupCoh».«d₁₀_apply_eq_sum» := P2M_GroundTheory_GroupCoh_d___apply_eq_sum_78c801493460
