-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_nrm_sub_le_of_le__5fdbf955fbfb
-- name    : P2M_GroundTheory_PAdicHodge_nrm_sub_le_of_le__5fdbf955fbfb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:51.765799+00:00
-- url     : https://prove2.me/theorems/5ad24046-5166-43be-87dc-694327728f26
-- title:
--   P2 M Ground Theory PAdic Hodge nrm sub le of le  5fdbf955fbfb: P2 M Ground Theory PAdic Hodge nrm sub le of le  5fdbf955fbfb
-- statement:
--   The P2 M Ground Theory PAdic Hodge nrm sub le of le  5fdbf955fbfb construction uses the P2 M Ground Theory PAdic Hodge nrm sub le of le  5fdbf955fbfb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L103-L107

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
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {K}

theorem P2M_GroundTheory_PAdicHodge_nrm_sub_le_of_le__5fdbf955fbfb {x y z : Ω} {r : ℝ} (h₁ : nrm K (x - y) ≤ r) (h₂ : nrm K (y - z) ≤ r) :
    nrm K (x - z) ≤ r := by sorry

alias «GroundTheory».«PAdicHodge».«nrm_sub_le_of_le'» := P2M_GroundTheory_PAdicHodge_nrm_sub_le_of_le__5fdbf955fbfb
