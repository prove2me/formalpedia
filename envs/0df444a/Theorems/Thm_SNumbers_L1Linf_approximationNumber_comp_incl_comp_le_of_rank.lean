-- Prove2me | Theorems.Thm_SNumbers_L1Linf_approximationNumber_comp_incl_comp_le_of_rank
-- name    : SNumbers.L1Linf.approximationNumber_comp_incl_comp_le_of_rank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:49.240181+00:00
-- url     : https://prove2.me/theorems/4791e822-4aa8-4a00-9709-1cccfc21ee95
-- title:
--   L1 Linf: approximation Number comp incl comp le of rank
-- statement:
--   **The key estimate, for `A` of finite rank.** If `A` has rank at most `m`,
--   then `aₙ(B I A) ≤ ‖A‖ ‖B‖ / (n+1)` for every `n`.
--
--   `T := B I A` has finite rank, hence is compact, and factors as `T = T₂T₁` through
--   `ℓ₂`; the two Hilbert–Schmidt bounds above then feed the general singular value
--   estimate `SVD.mul_approximationNumber_le_of_factorization`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L529-L539
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L529-L539

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

theorem SNumbers.L1Linf.approximationNumber_comp_incl_comp_le_of_rank {m : ℕ}
    (hrank : A.rank ≤ (m : Cardinal)) (n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by sorry
