-- Prove2me | Theorems.Thm_SVD_isClosed_isApproximable
-- name    : SVD.isClosed_isApproximable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:21.905753+00:00
-- url     : https://prove2.me/theorems/37786570-3963-54af-b484-2e9793f76d5a
-- title:
--   SVD: is Closed is Approximable
-- statement:
--   Approximable operators form a closed subset of `X →L[𝕜] Y`.
--
--   For any `S` in the closure of the approximable operators and `ε > 0`:
--   * pick approximable `T` with `‖S - T‖ < ε/2`;
--   * pick `N` with `aₙ(T) < ε/2` for all `n ≥ N`;
--   * by (S2), `aₙ(S) ≤ aₙ(T) + ‖S - T‖ < ε` for `n ≥ N`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L244-L275
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L244-L275

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

theorem SVD.isClosed_isApproximable :
    IsClosed { S : X →L[𝕜] Y | IsApproximable S } := by sorry
