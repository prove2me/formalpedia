-- Prove2me | Theorems.Thm_SNumbers_sn_smul_le
-- name    : SNumbers.sn_smul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:20:05.138191+00:00
-- url     : https://prove2.me/theorems/dcf2f52c-8092-483c-ac58-1a1b11c15a18
-- title:
--   SNumbers: sn smul le
-- statement:
--   **Forward homogeneity.** `sₙ(c • T) ≤ ‖c‖ · sₙ(T)`, directly from the
--   (S3) ideal property applied to `c • T = (c • id_Y) ∘ T ∘ id_X`
--   (with `‖c • id_Y‖ ≤ ‖c‖` and `‖id_X‖ ≤ 1`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L334-L353
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L334-L353

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

theorem SNumbers.sn_smul_le {s : Family 𝕜} (hs : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (c : 𝕜) (T : X →L[𝕜] Y) (n : ℕ) :
    s (c • T) n ≤ ‖c‖ * s T n := by sorry
