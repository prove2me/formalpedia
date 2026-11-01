-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_finiteZ_eq_sum_zpow_chargeEnergySectors
-- name    : QseriesFormalization.PartI.Ch04Franklin.finiteZ_eq_sum_zpow_chargeEnergySectors
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:24:34.56534+00:00
-- url     : https://prove2.me/theorems/dfd3ae84-dec7-46d9-be95-49c8f1a85e12
-- title:
--   Finite boson-fermion state sum grouped by charge sector
-- statement:
--   For every natural number $N$ and all complex $q,z$, the bounded partition function $Z_N(q,z)$ (the sum of $z^{\text{charge}}q^{\text{energy}}$ over pairs of subsets of the first $N$ modes, recording added particles and removed holes) can be grouped by the charge $c$ of the state:
--   $$Z_N(q,z)=\sum_{c\in\mathrm{Spec}_N}z^{c}\,E_{N,c}(q),$$
--   where $\mathrm{Spec}_N$ is the finite set of charge values occurring among bounded states and $E_{N,c}(q)$ is the sum of $q^{\text{energy}}$ over bounded states of charge $c$. This is a bookkeeping step in the Chapter 5 boson-fermion derivation of the Jacobi triple product.
--
--   Integer powers and reciprocals use Lean’s totalized convention: $0^{-1}=0$, so $0$ raised to a negative integer is $0$. The usual reciprocal interpretation applies when the base is nonzero.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter05_BosonFermion.lean#L807-L814

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

theorem QseriesFormalization.PartI.Ch04Franklin.finiteZ_eq_sum_zpow_chargeEnergySectors (N : Nat) (q z : ℂ) :
    finiteZ N q z =
      ∑ c ∈ finiteChargeSpectrum N, z ^ c * finiteChargeEnergySector N q c := by sorry
