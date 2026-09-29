-- Prove2me | Theorems.Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
-- name    : PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/bebf56cf-67a5-5a93-a054-dbe2bcd6b4e4
-- title:
--   Cyclic index-N sublattices come from primitive coset representatives
-- statement:
--   Let $N$ be a nonzero natural number and let $L$, $L'$ be period pairs, i.e. pairs of complex numbers independent over $\mathbb{R}$, each spanning a lattice in $\mathbb{C}$. Assume that the lattice of $L'$ is contained, as a subset of $\mathbb{C}$, in the lattice of $L$; that [`PeriodPair.sublatticeIndex L L'`](def/PeriodPair_Uniformization.html#L136), the index of the lattice of $L'$ viewed as a subgroup of the lattice of $L$, equals $N$; and that the corresponding quotient group [`PeriodPair.sublatticeQuotient L L'`](def/PeriodPair_Uniformization.html#L139) is additively cyclic. The conclusion asserts the existence of natural numbers $a$, $b$, $d$ and points $\tau$, $\sigma$ of the upper half-plane such that $(a,b,d)$ lies in [`ModularCurve.primCosetReps N`](def/ModularCurve_PrimCosetReps.html#L8), that is, $a$, $b$, $d$ are all at most $N$ and satisfy $ad = N$, $b < d$ and $\gcd(a,\gcd(b,d)) = 1$; such that $\sigma = (a\tau + b)/d$ as complex numbers; and such that the $j$-invariants match, $L$ with the period pair $(\tau, 1)$ and $L'$ with the period pair $(\sigma, 1)$. Here the $j$-invariant of a period pair is $1728\,g_2^3/(g_2^3 - 27 g_3^2)$ formed from its weight-four and weight-six lattice invariants.
--
--   This is the classical normalisation of a cyclic $N$-isogeny of complex tori: after a homothety, which leaves the $j$-invariant unchanged, a lattice and a cyclic sublattice of index $N$ become $\mathbb{Z}\tau + \mathbb{Z}$ and $\mathbb{Z}\sigma + \mathbb{Z}$ with $\sigma = (a\tau+b)/d$ for one of the primitive coset representatives of level $N$. It feeds the proof that the modular polynomial of level $N$ vanishes at the pair of $j$-invariants, [`ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic`](thm.html#ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
    {N : ℕ} [NeZero N] (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    ∃ (a b d : ℕ) (τ σ : ℍ), (a, b, d) ∈ ModularCurve.primCosetReps N ∧
      (σ : ℂ) = ((a : ℂ) * τ + b) / d ∧
      L.jLattice = (PeriodPair.ofTau τ).jLattice ∧ L'.jLattice = (PeriodPair.ofTau σ).jLattice := by sorry
