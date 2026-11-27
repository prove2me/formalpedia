-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_Nto_add_sub_le___3ec02eeaf1ce
-- name    : P2M_GroundTheory_PAdicHodge_NormTower_nrm_Nto_add_sub_le___3ec02eeaf1ce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:26.547843+00:00
-- url     : https://prove2.me/theorems/6fcd49c5-f6c3-4796-99e5-60b93a81e71c
-- title:
--   P2 M Ground Theory PAdic Hodge Norm Tower nrm Nto add sub le   3ec02eeaf1ce: P2 M Ground Theory PAdic Hodge Norm Tower nrm Nto add sub le   3ec02eeaf1ce
-- statement:
--   The P2 M Ground Theory PAdic Hodge Norm Tower nrm Nto add sub le   3ec02eeaf1ce construction uses the P2 M Ground Theory PAdic Hodge Norm Tower nrm Nto add sub le   3ec02eeaf1ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsRing.lean#L81-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsRing.lean#L81-L101

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
open GroundTheory.PAdicHodge.NormTower
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
  (t : NormTower K Ω p)

theorem P2M_GroundTheory_PAdicHodge_NormTower_nrm_Nto_add_sub_le___3ec02eeaf1ce (i : ℕ) {j : ℕ} {a b : Ω} (ha : a ∈ t.E (i + j)) (hb : b ∈ t.E (i + j))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) :
    nrm K (t.Nto i j (a + b) - t.Nto i j a - t.Nto i j b) ≤ t.ρ := by sorry

alias «GroundTheory».«PAdicHodge».«NormTower».«nrm_Nto_add_sub_le_ρ» := P2M_GroundTheory_PAdicHodge_NormTower_nrm_Nto_add_sub_le___3ec02eeaf1ce
