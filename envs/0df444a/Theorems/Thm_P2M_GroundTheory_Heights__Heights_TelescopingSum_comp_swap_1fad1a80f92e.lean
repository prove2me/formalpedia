-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TelescopingSum_comp_swap_1fad1a80f92e
-- name    : P2M_GroundTheory_Heights__Heights_TelescopingSum_comp_swap_1fad1a80f92e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:00.011298+00:00
-- url     : https://prove2.me/theorems/f5c64e3d-fb67-49ac-a65b-bfd132ef05bc
-- title:
--   P2 M Ground Theory Heights  Heights Telescoping Sum comp swap 1fad1a80f92e: P2 M Ground Theory Heights  Heights Telescoping Sum comp swap 1fad1a80f92e
-- statement:
--   The P2 M Ground Theory Heights  Heights Telescoping Sum comp swap 1fad1a80f92e construction uses the P2 M Ground Theory Heights  Heights Telescoping Sum comp swap 1fad1a80f92e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PTelescope.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PTelescope.lean#L14-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PTelescope
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.TelescopingSum

theorem P2M_GroundTheory_Heights__Heights_TelescopingSum_comp_swap_1fad1a80f92e {α : Type*} (D k : ℕ) (hk : k < D + 1) (X Y : α) (m : ℕ) (hm : m = k ∨ m = k + 1) :
    (fun j : Fin (D + 1) => if (j : ℕ) < m then X else Y) ∘ Equiv.swap ⟨k, hk⟩ (Fin.last D) =
      Fin.snoc (fun j : Fin D => if (j : ℕ) < k then X else Y) (if k < m then X else Y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TelescopingSum».«comp_swap» := P2M_GroundTheory_Heights__Heights_TelescopingSum_comp_swap_1fad1a80f92e
