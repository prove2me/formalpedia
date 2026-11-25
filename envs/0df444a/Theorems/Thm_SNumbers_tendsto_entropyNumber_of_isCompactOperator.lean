-- Prove2me | Theorems.Thm_SNumbers_tendsto_entropyNumber_of_isCompactOperator
-- name    : SNumbers.tendsto_entropyNumber_of_isCompactOperator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:37:21.849148+00:00
-- url     : https://prove2.me/theorems/1fdc2598-31d4-4480-8b31-35ba34aa0804
-- title:
--   SNumbers: tendsto entropy Number of is Compact Operator
-- statement:
--   **A compact operator has entropy numbers tending to zero.** No
--   completeness assumption is needed.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L343-L350
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L343-L350

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

theorem SNumbers.tendsto_entropyNumber_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) :
    Tendsto (entropyNumber S) atTop (𝓝 0) := by sorry
