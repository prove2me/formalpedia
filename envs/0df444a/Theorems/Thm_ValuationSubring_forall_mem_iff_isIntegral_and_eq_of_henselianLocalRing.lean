-- Prove2me | Theorems.Thm_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
-- name    : ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/db645e27-3e91-5148-aa95-30d422958a84
-- title:
--   Henselian valuation rings extend uniquely to algebraic extensions
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra that is algebraic over $K$, let $O$ be a valuation subring of $K$ whose underlying local ring is henselian, and let $V$ be a valuation subring of $L$ lying over $O$, in the sense that for every $x \in K$ one has $\mathrm{algebraMap}_{K,L}(x) \in V$ if and only if $x \in O$. The conclusion is a conjunction of two assertions. First, $V$ is precisely the integral closure of $O$ in $L$: for every $x \in L$, $x \in V$ if and only if $x$ is integral over $O$. Second, $V$ is the only valuation subring of $L$ with this property: any valuation subring $V'$ of $L$ such that, for all $x \in K$, $\mathrm{algebraMap}_{K,L}(x) \in V'$ if and only if $x \in O$, is equal to $V$. No finiteness is assumed on $L/K$ and no restriction is placed on the rank of $O$.
--
--   This is the implication from Hensel's lemma to uniqueness of prolongations in the classical theory of henselian valued fields, in the form that allows one to speak of *the* valuation subring of an algebraic extension of a henselian valued field, identified with the integral closure. It is used here to pin down valuation subrings of level fields of modular curves, as in the results on Igusa-type integrality over full-level structures that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (O : ValuationSubring K) [HenselianLocalRing O]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (∀ x : L, x ∈ V ↔ IsIntegral O x) ∧
      ∀ V' : ValuationSubring L, (∀ x : K, algebraMap K L x ∈ V' ↔ x ∈ O) → V' = V := by sorry
