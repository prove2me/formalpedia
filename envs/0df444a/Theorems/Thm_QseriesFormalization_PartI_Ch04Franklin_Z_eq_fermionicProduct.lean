-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_Z_eq_fermionicProduct
-- name    : QseriesFormalization.PartI.Ch04Franklin.Z_eq_fermionicProduct
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:23:15.956551+00:00
-- url     : https://prove2.me/theorems/1c525596-1089-4104-a2ca-a967abf95655
-- title:
--   Infinite boson-fermion partition function equals the fermionic product
-- statement:
--   For $q,z\in\mathbb{C}$ with $|q|<1$ and $z\ne0$, the full partition function $Z(q,z)=\sum_S z^{\text{charge}(S)}q^{\text{energy}(S)}$ over admissible states $S$ (finite configurations of added particles and removed holes, energy of mode $n$ equal to $n+1$) satisfies
--   $$Z(q,z)=\prod_{n\ge0}(1+zq^{n+1})(1+z^{-1}q^{n+1}).$$
--   This is the infinite fermionic evaluation in Chapter 5's boson-fermion proof of the Jacobi triple product.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_BosonFermion.lean#L474-L478

import Definitions.Def_QseriesFormalization_Chapter05_BosonFermion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chapter 5 Boson-Fermion partition function

This file adds the Chapter 5 partition-function layer on top of the
`AdmissibleState` setup in `Chapter05.lean`.

The global partition function is the formal/infinite sum over all admissible
states.  The closed proofs below are finite-mode versions: for modes
`0, ..., N - 1`, the state sum factors into the fermionic product over
single-mode occupations, and the same finite sum decomposes by charge sector.

The energy convention is the one already present in `Chapter05.lean`:
mode `n` contributes `n + 1`, avoiding half-powers.
-/

open QseriesFormalization
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch04Franklin

open scoped BigOperators
open Filter
open scoped Topology

/-! ### Infinite fermionic side -/

theorem QseriesFormalization.PartI.Ch04Franklin.Z_eq_fermionicProduct (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Z q z = fermionicProduct q z := by sorry
