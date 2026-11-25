-- Prove2me | Theorems.Thm_SVD_IsApproximable_add
-- name    : SVD.IsApproximable.add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:28.132245+00:00
-- url     : https://prove2.me/theorems/1a063162-a4e8-48a6-9447-c1a0f352dfa7
-- title:
--   Is Approximable: add
-- statement:
--   Sum of approximable operators is approximable. The proof goes through
--   the equivalent finite-rank-limit characterisation
--   (`isApproximable_iff_existsLimit`): given approximating sequences
--   `Lₘ → S` and `Kₘ → T`, the approximant
--   `Lₙ/₂ + Kₙ₋ₙ/₂ : X →L[𝕜] Y` has rank `≤ ⌊n/2⌋ + ⌈n/2⌉ = n` (using
--   `LinearMap.rank_add_le`) and residual `≤ ‖S - Lₙ/₂‖ + ‖T - Kₙ₋ₙ/₂‖ → 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L193-L234
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L193-L234

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

theorem SVD.IsApproximable.add {S T : X →L[𝕜] Y}
    (hS : IsApproximable S) (hT : IsApproximable T) :
    IsApproximable (S + T) := by sorry
