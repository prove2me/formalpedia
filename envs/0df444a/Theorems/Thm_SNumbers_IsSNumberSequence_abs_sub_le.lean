-- Prove2me | Theorems.Thm_SNumbers_IsSNumberSequence_abs_sub_le
-- name    : SNumbers.IsSNumberSequence.abs_sub_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:26:27.176912+00:00
-- url     : https://prove2.me/theorems/e9e24428-d4a0-5adc-abc3-ec1457313807
-- title:
--   Is SNumber Sequence: abs sub le
-- statement:
--   Every s-number sequence is `1`-Lipschitz in the operator at a fixed index:
--   `|sₙ(S) − sₙ(T)| ≤ ‖S − T‖`. Both one-sided bounds are (S2), applied to `S = T + (S − T)`
--   and to `T = S + (T − S)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L219-L227
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L219-L227

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

theorem SNumbers.IsSNumberSequence.abs_sub_le {s : Family 𝕜} (h : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (n : ℕ) :
    |s S n - s T n| ≤ ‖S - T‖ := by sorry
