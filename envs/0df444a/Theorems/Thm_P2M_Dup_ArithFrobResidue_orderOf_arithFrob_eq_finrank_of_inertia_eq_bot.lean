-- Prove2me | Theorems.Thm_P2M_Dup_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
-- name    : P2M.Dup.ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/dcef54b4-7a88-596b-85eb-75d0a37f590e
-- title:
--   Order of arithmetic Frobenius equals the residue degree
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $G$ be a group acting on $B$ by ring automorphisms in a way compatible with the $A$-action (so that the action commutes with multiplication by elements of $A$). Let $P$ be a maximal ideal of $B$ whose contraction $P\cap A$ (written `P.under A`) is a maximal ideal of $A$, and assume both residue rings are finite, $A/(P\cap A)$ being equipped with a `Fintype` structure and $B/P$ being finite; by the local instance making quotients by maximal ideals fields, these are finite fields. Assume further that the inertia subgroup of $P$ in $G$ — the subgroup of elements of the stabiliser of $P$ acting trivially on $B/P$ — is trivial, $P.\mathrm{inertia}\,G=\bot$. Let $\sigma$ be an element of the stabiliser of $P$ in $G$ which is an arithmetic Frobenius at $P$ over $A$, i.e. $\sigma$ raises every element of $B$ to the power $\#\,A/(P\cap A)$ modulo $P$. Then the order of $\sigma$ as an element of $G$ equals the residue degree $[\,B/P : A/(P\cap A)\,]$, i.e. $\operatorname{finrank}_{A/(P\cap A)}(B/P)$.
--
--   This is the standard statement that at an unramified maximal ideal the arithmetic Frobenius has order exactly the residue degree $f$, so that it generates the decomposition group, a cyclic group of order $f$. It is used in the Langlands–Tunnell part of the development, where Frobenius elements of prescribed order control the cycle types of the permutation actions attached to cubic resolvents and the construction of Hecke characters from Galois data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot.lean

import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_ArithFrobResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise
attribute [local instance] Ideal.Quotient.field

theorem P2M.Dup.ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    (hP : P.inertia G = ⊥)
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (σ : G) = Module.finrank (A ⧸ P.under A) (B ⧸ P) := by sorry
