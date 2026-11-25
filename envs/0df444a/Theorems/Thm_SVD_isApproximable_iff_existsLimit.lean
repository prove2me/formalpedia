-- Prove2me | Theorems.Thm_SVD_isApproximable_iff_existsLimit
-- name    : SVD.isApproximable_iff_existsLimit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:21:42.097303+00:00
-- url     : https://prove2.me/theorems/76c53500-bf21-485c-81ee-facf5aef23bc
-- title:
--   SVD: is Approximable iff exists Limit
-- statement:
--   Equivalent characterisation: approximable iff a uniform limit of
--   finite-rank operators. The forward direction extracts a near-optimal
--   rank-`≤ n` approximant `Lₙ` with `‖S - Lₙ‖ < aₙ(S) + 1/(n+1)`; the
--   converse uses `approximationNumber_le_norm_sub` and squeeze.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L69-L107
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L69-L107

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SVD.isApproximable_iff_existsLimit (S : X →L[𝕜] Y) :
    IsApproximable S ↔
      ∃ L : ℕ → X →L[𝕜] Y, (∀ n, (L n).rank ≤ (n : Cardinal)) ∧
        Tendsto (fun n => ‖S - L n‖) atTop (𝓝 0) := by sorry
