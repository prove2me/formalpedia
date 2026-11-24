-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144
-- name    : P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:20.174686+00:00
-- url     : https://prove2.me/theorems/3ecaf217-9557-4540-ab2b-d471f10a83ed
-- title:
--   P2 M Ground Theory Group Coh tensor   tmul caf50afb1144: P2 M Ground Theory Group Coh tensor   tmul caf50afb1144
-- statement:
--   The P2 M Ground Theory Group Coh tensor   tmul caf50afb1144 construction uses the P2 M Ground Theory Group Coh tensor   tmul caf50afb1144 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L222-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L222-L224

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}

theorem P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144 (X Y : Rep k G) (s : G) (a : X) (b : Y) :
    (X ⊗ Y).ρ s (a ⊗ₜ[k] b) = X.ρ s a ⊗ₜ[k] Y.ρ s b := by sorry

alias «GroundTheory».«GroupCoh».«tensor_ρ_tmul» := P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144
