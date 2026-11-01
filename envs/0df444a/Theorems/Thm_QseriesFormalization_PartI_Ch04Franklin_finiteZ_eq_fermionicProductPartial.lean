-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_finiteZ_eq_fermionicProductPartial
-- name    : QseriesFormalization.PartI.Ch04Franklin.finiteZ_eq_fermionicProductPartial
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:24:30.92499+00:00
-- url     : https://prove2.me/theorems/111fd634-c00c-4ca3-a510-3960f0628c9f
-- title:
--   Finite boson-fermion state sum equals a finite fermionic product
-- statement:
--   Let $N\in\mathbb{N}$ and $q,z\in\mathbb{C}$ with $z\ne0$. The bounded partition function $Z_N(q,z)$, a sum of $z^{\text{charge}}q^{\text{energy}}$ over pairs of subsets $(A,B)$ of the first $N$ modes (added particles and removed holes), factors as
--   $$Z_N(q,z)=\prod_{n=0}^{N-1}(1+zq^{n+1})\cdot\prod_{n=0}^{N-1}(1+z^{-1}q^{n+1}).$$
--   This is a finite statement in the Chapter 5 boson-fermion derivation of the Jacobi triple product.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_BosonFermion.lean#L230-L253

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

theorem QseriesFormalization.PartI.Ch04Franklin.finiteZ_eq_fermionicProductPartial (N : Nat) (q z : ℂ) (hz : z ≠ 0) :
    finiteZ N q z = fermionicProductPartial N q z := by sorry
