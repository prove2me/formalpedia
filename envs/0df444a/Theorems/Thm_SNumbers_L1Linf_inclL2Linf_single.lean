-- Prove2me | Theorems.Thm_SNumbers_L1Linf_inclL2Linf_single
-- name    : SNumbers.L1Linf.inclL2Linf_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:42:31.384902+00:00
-- url     : https://prove2.me/theorems/d32c6edc-7509-422c-b3ef-9c3d6ed602dd
-- title:
--   L1 Linf: incl L2 Linf single
-- statement:
--   `J₂` maps the `j`-th unit vector of `ℓ₂` to the `j`-th unit vector of `ℓ_∞`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L418-L420
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L418-L420

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

theorem SNumbers.L1Linf.inclL2Linf_single (j : ℕ) :
    (inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜) (lp.single 2 j (1 : 𝕜)) = lp.single ∞ j (1 : 𝕜) := by sorry
