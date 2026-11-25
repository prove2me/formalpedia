-- Prove2me | Theorems.Thm_SNumbers_L1Linf_one_div_le_hilbertNumber
-- name    : SNumbers.L1Linf.one_div_le_hilbertNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:13:37.095522+00:00
-- url     : https://prove2.me/theorems/20d2b1db-1177-594c-bb72-5c68629fdc3e
-- title:
--   L1 Linf: one div le hilbert Number
-- statement:
--   The Hilbert numbers of `I : ℓ₁ → ℓ_∞` are bounded below by `1/(n+1)`. Combined with
--   `cₙ(I) ≥ ½`, this shows the factor `n+1` in the maximal difference theorem is order-optimal.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L309-L336
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L309-L336

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

theorem SNumbers.L1Linf.one_div_le_hilbertNumber (n : ℕ) :
    (1 : ℝ) / (n + 1) ≤ hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by sorry
