-- Prove2me | Theorems.Thm_SNumbers_tendsto_entropyNumber_iff_totallyBounded
-- name    : SNumbers.tendsto_entropyNumber_iff_totallyBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:03.177812+00:00
-- url     : https://prove2.me/theorems/ba0b07e0-7669-4dd2-8b24-29c0a64e63f7
-- title:
--   SNumbers: tendsto entropy Number iff totally Bounded
-- statement:
--   **The entropy numbers of `S` tend to `0` exactly when `S(B_X)` is totally
--   bounded.** Both statements say that the image of the unit ball admits finite
--   `ε`-nets for every `ε > 0`; the entropy numbers merely package the size of
--   those nets into a sequence.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L315-L339
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L315-L339

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

theorem SNumbers.tendsto_entropyNumber_iff_totallyBounded (S : X →L[𝕜] Y) :
    Tendsto (entropyNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) := by sorry
