-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_bosonFermion_JTP
-- name    : QseriesFormalization.PartI.Ch04Franklin.bosonFermion_JTP
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:23:45.208226+00:00
-- url     : https://prove2.me/theorems/8fea5274-dd95-42e1-a20a-0df6c2d76bbf
-- title:
--   Boson-fermion derivation of the shifted Jacobi triple product
-- statement:
--   For $q,z\in\mathbb{C}$ with $|q|<1$ and $z\ne0$, with $Z(q,z)$ the boson-fermion partition function (see the previous statement),
--   $$(1+z^{-1})\,Z(q,z)\prod_{n\ge0}(1-q^{n+1})=\sum_{n\in\mathbb{Z}}z^{n}q^{n(n+1)/2}.$$
--   Combined with the fermionic product for $Z$ this is the Jacobi triple product in a shifted form, and the statement is the Chapter 5 physical (boson-fermion correspondence) proof of it.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_BosonFermion.lean#L767-L779

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

/-! ### Boson-Fermion product side as Jacobi's triple product -/

theorem QseriesFormalization.PartI.Ch04Franklin.bosonFermion_JTP (q z : ℂ)
    (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (1 + z⁻¹) * Z q z * bosonEulerProduct q =
      bosonFermionThetaSeries q z := by sorry
