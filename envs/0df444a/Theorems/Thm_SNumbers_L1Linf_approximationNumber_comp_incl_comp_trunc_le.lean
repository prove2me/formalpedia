-- Prove2me | Theorems.Thm_SNumbers_L1Linf_approximationNumber_comp_incl_comp_trunc_le
-- name    : SNumbers.L1Linf.approximationNumber_comp_incl_comp_trunc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:15:50.791256+00:00
-- url     : https://prove2.me/theorems/822be766-7adf-5c24-9ce7-1be23ec41de7
-- title:
--   L1 Linf: approximation Number comp incl comp trunc le
-- statement:
--   The key estimate for the truncations: `aₙ(B I Aₘ) ≤ ‖A‖ ‖B‖ / (n+1)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L593-L599
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L593-L599

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

theorem SNumbers.L1Linf.approximationNumber_comp_incl_comp_trunc_le (m n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (trunc A m))) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by sorry
