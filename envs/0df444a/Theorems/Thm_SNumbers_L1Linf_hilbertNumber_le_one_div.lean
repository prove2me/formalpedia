-- Prove2me | Theorems.Thm_SNumbers_L1Linf_hilbertNumber_le_one_div
-- name    : SNumbers.L1Linf.hilbertNumber_le_one_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:16:12.275997+00:00
-- url     : https://prove2.me/theorems/3b766e14-6c9a-5a76-b1f9-03eb5cb9a551
-- title:
--   L1 Linf: hilbert Number le one div
-- statement:
--   The Hilbert numbers of `I : ℓ₁ → ℓ_∞` are bounded above by `1/(n+1)`: every
--   admissible ratio `aₙ(B I A)/(‖B‖‖A‖)` is, by the key estimate.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L669-L678
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L669-L678

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

theorem SNumbers.L1Linf.hilbertNumber_le_one_div (n : ℕ) :
    hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n ≤ (1 : ℝ) / (n + 1) := by sorry
