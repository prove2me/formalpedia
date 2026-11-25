-- Prove2me | Theorems.Thm_SNumbers_norm_smul_le_sn
-- name    : SNumbers.norm_smul_le_sn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:20:13.486891+00:00
-- url     : https://prove2.me/theorems/60248d2c-9d56-4c43-8573-fddcddb030a9
-- title:
--   SNumbers: norm smul le sn
-- statement:
--   **Reverse homogeneity.** For a nonzero scalar `c`, `‖c‖ · sₙ(T) ≤ sₙ(c • T)`.
--
--   Apply `sn_smul_le` to the operator `c • T` with `c` replaced by `c⁻¹`:
--   `sₙ(T) = sₙ(c⁻¹ • (c • T)) ≤ ‖c‖⁻¹ · sₙ(c • T)`; then multiply by `‖c‖ > 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L359-L369
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L359-L369

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

theorem SNumbers.norm_smul_le_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {c : 𝕜} (hc : c ≠ 0) (T : X →L[𝕜] Y) (n : ℕ) :
    ‖c‖ * s T n ≤ s (c • T) n := by sorry
