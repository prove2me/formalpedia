-- Prove2me | Theorems.Thm_SNumbers_IsSNumberSequence_le_norm
-- name    : SNumbers.IsSNumberSequence.le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:29.466242+00:00
-- url     : https://prove2.me/theorems/05c689d9-7b9a-467f-a781-d84c4d041b6e
-- title:
--   Is SNumber Sequence: le norm
-- statement:
--   Every s-number sequence is bounded by the operator norm: `sₙ S ≤ ‖S‖`.
--
--   This is the common reason behind the individual `…_le_norm` lemmas for each
--   concrete s-number: since `s` is non-increasing in `n` (`antitone`) and `s₀ = ‖S‖`
--   (`norm_at_zero`), we get `sₙ S ≤ s₀ S = ‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L210-L214
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L210-L214

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

theorem SNumbers.IsSNumberSequence.le_norm {s : Family 𝕜} (h : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ ‖S‖ := by sorry
