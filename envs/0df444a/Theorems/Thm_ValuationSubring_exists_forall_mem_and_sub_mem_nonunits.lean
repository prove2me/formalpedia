-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
-- name    : ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/ee407444-7d62-5e8a-b78d-8ee18490a3a9
-- title:
--   Residue-level approximation for incomparable valuation rings
-- statement:
--   Let $K$ be a field and let $\iota$ be a finite index type. Let $R : \iota \to \mathrm{ValuationSubring}\,K$ be a family of valuation subrings of $K$, assumed pairwise incomparable in the strong sense that for all indices $i, j$, the inclusion $R_i \le R_j$ forces $i = j$ (so in particular the family is injective, and for $i \neq j$ neither of $R_i$, $R_j$ contains the other). Let $a : \iota \to K$ be a family of elements with $a_i \in R_i$ for every $i$. The conclusion is the existence of a single element $z \in K$ such that for every $i$ one has both $z \in R_i$ and $z - a_i \in (R_i).\mathrm{nonunits}$, the latter being the set of elements of $K$ that are non-units of $R_i$, i.e. the maximal ideal of $R_i$ regarded as a subset of $K$ (equivalently, those $x$ with $v_i(x) < 1$ for the valuation $v_i$ attached to $R_i$). Thus $z$ lies in $\bigcap_i R_i$ and satisfies $z \equiv a_i \pmod{\mathfrak m_i}$ simultaneously for all $i$; no independence of the valuations is assumed beyond incomparability.
--
--   This is the weak, residue-level form of the approximation theorem for finitely many valuations of a field: it says that the canonical map $\bigcap_i R_i \to \prod_i R_i/\mathfrak m_i$ is surjective for pairwise incomparable valuation rings, a hypothesis satisfied by the several prolongations of a single valuation of a subfield even when these are dependent. It is used in the treatment of regular prolongations on algebraic curves, for instance to produce elements with prescribed residues, elements with transcendental residue, and bases adapted to the product of residue fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    {K : Type*} [Field K] {ι : Type*} [Finite ι] (R : ι → ValuationSubring K)
    (hR : ∀ i j, R i ≤ R j → i = j) (a : ι → K) (ha : ∀ i, a i ∈ R i) :
    ∃ z : K, ∀ i, z ∈ R i ∧ z - a i ∈ (R i).nonunits := by sorry
