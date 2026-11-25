-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_add_sub_le___484fd36eb6a8
-- name    : P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_add_sub_le___484fd36eb6a8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:59.298803+00:00
-- url     : https://prove2.me/theorems/011b39d3-f61a-44ac-8762-b5aac090489c
-- title:
--   P2 M Ground Theory PAdic Hodge Norm Tower nrm N add sub le   484fd36eb6a8: P2 M Ground Theory PAdic Hodge Norm Tower nrm N add sub le   484fd36eb6a8
-- statement:
--   The P2 M Ground Theory PAdic Hodge Norm Tower nrm N add sub le   484fd36eb6a8 construction uses the P2 M Ground Theory PAdic Hodge Norm Tower nrm N add sub le   484fd36eb6a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L457-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L457-L468

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
open GroundTheory.PAdicHodge.NormTower
variable {K Ω p} (t : NormTower K Ω p)

theorem P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_add_sub_le___484fd36eb6a8 (n : ℕ) {a b : Ω} (ha : a ∈ t.E (n + 1)) (hb : b ∈ t.E (n + 1))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) :
    nrm K (t.N n (a + b) - t.N n a - t.N n b) ≤ t.ρ := by sorry

alias «GroundTheory».«PAdicHodge».«NormTower».«nrm_N_add_sub_le_ρ» := P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_add_sub_le___484fd36eb6a8
