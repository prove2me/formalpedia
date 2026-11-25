-- Prove2me | Theorems.Thm_SNumbers_L1Linf_hilbertNumber_eq_one_div
-- name    : SNumbers.L1Linf.hilbertNumber_eq_one_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:18:13.453685+00:00
-- url     : https://prove2.me/theorems/3899f730-891b-4b72-a7ed-8fe003eff0a0
-- title:
--   L1 Linf: hilbert Number eq one div
-- statement:
--   **The Hilbert numbers of the inclusion `I : ℓ₁ → ℓ_∞`:** `hₙ(I) = 1/(n+1)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L681-L683
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L681-L683

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

theorem SNumbers.L1Linf.hilbertNumber_eq_one_div (n : ℕ) :
    hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n = (1 : ℝ) / (n + 1) := by sorry
