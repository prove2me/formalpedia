-- Prove2me | Theorems.Thm_SNumbers_L1Linf_incl_eq_comp
-- name    : SNumbers.L1Linf.incl_eq_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:29:32.587954+00:00
-- url     : https://prove2.me/theorems/89909a9d-7c9d-5df4-b752-c78409935d15
-- title:
--   L1 Linf: incl eq comp
-- statement:
--   `I = J₂ ∘ J₁`: all three inclusions act as the identity on coordinates.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L412-L415
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L412-L415

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

theorem SNumbers.L1Linf.incl_eq_comp :
    (incl : L1 𝕜 →L[𝕜] Linf 𝕜)
      = (inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜).comp (inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜) := by sorry
