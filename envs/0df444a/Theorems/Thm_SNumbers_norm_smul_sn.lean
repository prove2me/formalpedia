-- Prove2me | Theorems.Thm_SNumbers_norm_smul_sn
-- name    : SNumbers.norm_smul_sn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:49.845979+00:00
-- url     : https://prove2.me/theorems/3009df57-018c-4086-b212-8cb251aafbed
-- title:
--   SNumbers: norm smul sn
-- statement:
--   **Absolute homogeneity of `s`-numbers.** `sₙ(c • T) = ‖c‖ · sₙ(T)` for
--   every scalar `c`: the direct combination of the one-sided inequalities
--   `sn_smul_le` and `norm_smul_le_sn`. (For `c = 0` the reverse direction is
--   just non-negativity (S1), since `‖0‖ · sₙ(T) = 0`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L375-L384
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L375-L384

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

theorem SNumbers.norm_smul_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (c : 𝕜) (T : X →L[𝕜] Y) (n : ℕ) :
    s (c • T) n = ‖c‖ * s T n := by sorry
