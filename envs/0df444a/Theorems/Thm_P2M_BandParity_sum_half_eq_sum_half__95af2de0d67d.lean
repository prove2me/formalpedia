-- Prove2me | Theorems.Thm_P2M_BandParity_sum_half_eq_sum_half__95af2de0d67d
-- name    : P2M_BandParity_sum_half_eq_sum_half__95af2de0d67d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:00.38896+00:00
-- url     : https://prove2.me/theorems/e8061839-cc81-53db-a685-c81a5e507cf2
-- title:
--   P2 M Band Parity sum half eq sum half  95af2de0d67d: P2 M Band Parity sum half eq sum half  95af2de0d67d
-- statement:
--   On the half range, a function vanishing at `0` may be summed over `0 < ⟨x⟩ < p/2`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L110-L118
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L110-L118

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_BandParity_sum_half_eq_sum_half__95af2de0d67d {R : Type*} [AddCommMonoid R] (h : ZMod p → R) (h0 : h 0 = 0) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), h x =
      ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p), h x := by sorry

alias «BandParity».«sum_half_eq_sum_half'» := P2M_BandParity_sum_half_eq_sum_half__95af2de0d67d
