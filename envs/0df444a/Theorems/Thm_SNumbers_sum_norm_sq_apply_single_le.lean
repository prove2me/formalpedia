-- Prove2me | Theorems.Thm_SNumbers_sum_norm_sq_apply_single_le
-- name    : SNumbers.sum_norm_sq_apply_single_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:25:37.588536+00:00
-- url     : https://prove2.me/theorems/b88abf8b-2ba3-48d7-b7e5-30c91e3ac095
-- title:
--   SNumbers: sum norm sq apply single le
-- statement:
--   **Little Grothendieck inequality for `ℓ_∞ → H`.** For every bounded operator
--   `B` from `ℓ_∞` into a Hilbert space and every finite set `J` of indices,
--   `∑_{j ∈ J} ‖B e_j‖² ≤ ‖B‖²`; that is, `B` is Hilbert–Schmidt on the unit vectors
--   with `‖B‖_HS ≤ ‖B‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L191-L205
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L191-L205

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [DecidableEq ι]

theorem SNumbers.sum_norm_sq_apply_single_le (B : lp (fun _ : ι => 𝕜) ∞ →L[𝕜] H) (J : Finset ι) :
    ∑ j ∈ J, ‖B (lp.single ∞ j (1 : 𝕜))‖ ^ 2 ≤ ‖B‖ ^ 2 := by sorry
