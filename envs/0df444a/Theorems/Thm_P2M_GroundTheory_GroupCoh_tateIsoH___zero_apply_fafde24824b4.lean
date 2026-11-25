-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateIsoH___zero_apply_fafde24824b4
-- name    : P2M_GroundTheory_GroupCoh_tateIsoH___zero_apply_fafde24824b4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:21.545446+00:00
-- url     : https://prove2.me/theorems/071f249e-f6d9-46d8-bc1e-340efec087df
-- title:
--   P2 M Ground Theory Group Coh tate Iso H   zero apply fafde24824b4: P2 M Ground Theory Group Coh tate Iso H   zero apply fafde24824b4
-- statement:
--   The P2 M Ground Theory Group Coh tate Iso H   zero apply fafde24824b4 construction uses the P2 M Ground Theory Group Coh tate Iso H   zero apply fafde24824b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateDeltaZero.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateDeltaZero.lean#L15-L49

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateDeltaZero
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
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}
  (hX : X.ShortExact)

theorem P2M_GroundTheory_GroupCoh_tateIsoH___zero_apply_fafde24824b4 (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) (c : (tateComplex X.X₃).cycles 0)
    (hc : ((tateComplex X.X₃).iCycles 0).hom c = (cochainsIso₀ X.X₃).inv.hom z) :
    (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom
      ((TateCohomology.δ hX 0).hom (((tateComplex X.X₃).homologyπ 0).hom c)) =
      H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by sorry

alias «GroundTheory».«GroupCoh».«tateIsoH_δ_zero_apply» := P2M_GroundTheory_GroupCoh_tateIsoH___zero_apply_fafde24824b4
