-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le___999ce6594f0e
-- name    : P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le___999ce6594f0e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:41.467796+00:00
-- url     : https://prove2.me/theorems/afc2a4d5-b800-4644-a06d-802479b267ab
-- title:
--   P2 M Ground Theory PAdic Hodge Norm Tower nrm N sub N le   999ce6594f0e: P2 M Ground Theory PAdic Hodge Norm Tower nrm N sub N le   999ce6594f0e
-- statement:
--   The P2 M Ground Theory PAdic Hodge Norm Tower nrm N sub N le   999ce6594f0e construction uses the P2 M Ground Theory PAdic Hodge Norm Tower nrm N sub N le   999ce6594f0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L447-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L447-L455

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

theorem P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le___999ce6594f0e (n : ℕ) {a b : Ω} (ha : a ∈ t.E (n + 1)) (hb : b ∈ t.E (n + 1))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) (hab : nrm K (a - b) ≤ t.ρ) :
    nrm K (t.N n a - t.N n b) ≤ t.ρ := by sorry

alias «GroundTheory».«PAdicHodge».«NormTower».«nrm_N_sub_N_le_ρ» := P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le___999ce6594f0e
