-- Prove2me | Theorems.Thm_SNumbers_isCompactOperator_iff_tendsto_entropyNumber
-- name    : SNumbers.isCompactOperator_iff_tendsto_entropyNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:05:19.406681+00:00
-- url     : https://prove2.me/theorems/8fef14a2-6f7d-4860-b682-99d3fa815bf3
-- title:
--   SNumbers: is Compact Operator iff tendsto entropy Number
-- statement:
--   **Compactness is measured by the entropy numbers**: for a complete target
--   space, `S` is a compact operator if and only if `e_n S → 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L364-L367
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L364-L367

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.isCompactOperator_iff_tendsto_entropyNumber [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ Tendsto (entropyNumber S) atTop (𝓝 0) := by sorry
