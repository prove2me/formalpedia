-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
-- name    : P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:13.718564+00:00
-- url     : https://prove2.me/theorems/9fc6f602-ede7-44a3-96a4-ac1fdc51ddca
-- title:
--   P2 M Ground Theory PAdic Hodge Norm Tower   lt one de857b87b125: P2 M Ground Theory PAdic Hodge Norm Tower   lt one de857b87b125
-- statement:
--   The P2 M Ground Theory PAdic Hodge Norm Tower   lt one de857b87b125 construction uses the P2 M Ground Theory PAdic Hodge Norm Tower   lt one de857b87b125 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L390-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L390-L390

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

theorem P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125 : t.ρ < 1 := by sorry

alias «GroundTheory».«PAdicHodge».«NormTower».«ρ_lt_one» := P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
