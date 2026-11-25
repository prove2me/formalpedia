-- Prove2me | Theorems.Thm_SNumbers_L1Linf_rank_trunc_le
-- name    : SNumbers.L1Linf.rank_trunc_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:50.514811+00:00
-- url     : https://prove2.me/theorems/4d723b37-708d-4a8a-9ada-b7edf2c156cb
-- title:
--   L1 Linf: rank trunc le
-- statement:
--   The truncation has rank at most `m`, since it factors through `ℓ₂ᵐ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L566-L569
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L566-L569

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)

theorem SNumbers.L1Linf.rank_trunc_le (m : ℕ) : (trunc A m).rank ≤ (m : Cardinal) := by sorry
