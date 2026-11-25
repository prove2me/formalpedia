-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_single_mem_span_e985f142ac72
-- name    : P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_single_mem_span_e985f142ac72
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:53.15987+00:00
-- url     : https://prove2.me/theorems/31477697-a8d9-4855-80ec-fd5111798c10
-- title:
--   P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG single mem span e985f142ac72: P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG single mem span e985f142ac72
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG single mem span e985f142ac72 construction uses the P2 M Ground Theory Heights  Heights KLines Ideal Lattice FG single mem span e985f142ac72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealLatticeFG.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealLatticeFG.lean#L24-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealLatticeFG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG

theorem P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_single_mem_span_e985f142ac72 (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) (hx : a x ≠ 0) :
    (Pi.single x 1 : Fin n → K) ∈ Submodule.span K (idealLattice a : Set (Fin n → K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesIdealLatticeFG».«single_mem_span» := P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_single_mem_span_e985f142ac72
