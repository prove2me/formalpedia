-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_pow_sub_pow_le___4bebacc7034d
-- name    : P2M_GroundTheory_PAdicHodge_NormTower_nrm_pow_sub_pow_le___4bebacc7034d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:47.527867+00:00
-- url     : https://prove2.me/theorems/a5b55cdc-71d8-4aa3-b5ed-a9d3d6909a3d
-- title:
--   P2 M Ground Theory PAdic Hodge Norm Tower nrm pow sub pow le   4bebacc7034d: P2 M Ground Theory PAdic Hodge Norm Tower nrm pow sub pow le   4bebacc7034d
-- statement:
--   The P2 M Ground Theory PAdic Hodge Norm Tower nrm pow sub pow le   4bebacc7034d construction uses the P2 M Ground Theory PAdic Hodge Norm Tower nrm pow sub pow le   4bebacc7034d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L443-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L443-L445

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

theorem P2M_GroundTheory_PAdicHodge_NormTower_nrm_pow_sub_pow_le___4bebacc7034d {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1)
    (hab : nrm K (a - b) ≤ t.ρ) (m : ℕ) : nrm K (a ^ m - b ^ m) ≤ t.ρ := by sorry

alias «GroundTheory».«PAdicHodge».«NormTower».«nrm_pow_sub_pow_le_ρ» := P2M_GroundTheory_PAdicHodge_NormTower_nrm_pow_sub_pow_le___4bebacc7034d
