-- Prove2me | Theorems.Thm_SNumbers_isCompactOperator_of_tendsto_entropyNumber
-- name    : SNumbers.isCompactOperator_of_tendsto_entropyNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:38:43.136176+00:00
-- url     : https://prove2.me/theorems/55bb8d10-367c-4c34-ac16-7be9878e21c3
-- title:
--   SNumbers: is Compact Operator of tendsto entropy Number
-- statement:
--   **Entropy numbers tending to zero force compactness**, provided the target
--   space is complete: a totally bounded set then has compact closure.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L354-L360
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L354-L360

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

theorem SNumbers.isCompactOperator_of_tendsto_entropyNumber [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : Tendsto (entropyNumber S) atTop (𝓝 0)) :
    IsCompactOperator S := by sorry
