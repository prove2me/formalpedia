-- Prove2me | Theorems.Thm_SNumbers_sum_powerset_norm_signedSum_sq
-- name    : SNumbers.sum_powerset_norm_signedSum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:25:27.105265+00:00
-- url     : https://prove2.me/theorems/5c9e668e-98df-4666-8aad-1cc7e8343a1b
-- title:
--   SNumbers: sum powerset norm signed Sum sq
-- statement:
--   **Sign averaging (identity form).** Summing `‖∑_j ε_j w_j‖²` over all `2^|J|`
--   sign patterns gives `2^|J| · ∑_{j ∈ J} ‖w_j‖²`: the cross terms cancel. The proof
--   is induction on `J`, where the two extensions of a sign pattern to a new index
--   are paired by the parallelogram law.
--
--   The scalar field `𝕜` is an explicit argument because it does not occur in the
--   statement (only the norm does, while the proof uses the inner product).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L109-L132
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L109-L132

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
variable {ι : Type*} [DecidableEq ι]

theorem SNumbers.sum_powerset_norm_signedSum_sq (𝕜 : Type*) [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (w : ι → H) (J : Finset ι) :
    ∑ S ∈ J.powerset, ‖signedSum w S J‖ ^ 2 = 2 ^ J.card * ∑ j ∈ J, ‖w j‖ ^ 2 := by sorry
