-- Prove2me | Theorems.Thm_SNumbers_L1Linf_mul_hilbertNumber_le_gelfandNumber
-- name    : SNumbers.L1Linf.mul_hilbertNumber_le_gelfandNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:39:28.266796+00:00
-- url     : https://prove2.me/theorems/a3487128-8dcd-425b-812d-9f1dd510ce94
-- title:
--   L1 Linf: mul hilbert Number le gelfand Number
-- statement:
--   **Order-optimality of the factor `n+1`** in the maximal difference theorem:
--   for the inclusion `I : ℓ₁ → ℓ_∞` one has `((n+1)/2) · hₙ(I) ≤ cₙ(I)`, whereas the
--   maximal difference theorem bounds `cₙ ≤ aₙ ≤ e·(n+1)·hₙ` from above. So the linear
--   growth of the factor cannot be improved.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L689-L695
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L689-L695

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

theorem SNumbers.L1Linf.mul_hilbertNumber_le_gelfandNumber (n : ℕ) :
    ((n : ℝ) + 1) / 2 * hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n
      ≤ gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by sorry
