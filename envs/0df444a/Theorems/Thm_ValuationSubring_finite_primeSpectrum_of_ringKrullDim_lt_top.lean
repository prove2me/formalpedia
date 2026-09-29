-- Prove2me | Theorems.Thm_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top
-- name    : ValuationSubring.finite_primeSpectrum_of_ringKrullDim_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/c4ea36e2-a781-5c0f-927f-abb2a07076dd
-- title:
--   Valuation rings of finite Krull dimension have finite spectrum
-- statement:
--   Let $L$ be a field and let $A$ be a valuation subring of $L$, that is, a subring of $L$ such that for every $x \in L$ either $x \in A$ or $x^{-1} \in A$. Assume that the Krull dimension of $A$, taken in Mathlib's sense as an element of $\mathbb{N}_\infty$ adjoined a bottom element (so that the empty ring receives $\bot$), satisfies $\operatorname{ringKrullDim} A < \top$; equivalently, the lengths of chains of prime ideals of $A$ are bounded. The conclusion is that the prime spectrum of $A$, the type of prime ideals of $A$ (equipped with its usual structure as a topological space, but here regarded only as a type), is finite, i.e. carries the `Finite` instance. No bound on the number of primes in terms of the dimension is asserted, only finiteness.
--
--   A valuation ring has totally ordered spectrum, so a bound on chain lengths bounds the number of primes outright; this is the standard finiteness statement for the spectrum of a finite-dimensional valuation ring. It is used in the study of regular prolongations on algebraic curves, where a valuation subring of finite Krull dimension must be handled by a finite case analysis over its primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.finite_primeSpectrum_of_ringKrullDim_lt_top
    {L : Type*} [Field L] (A : ValuationSubring L) (h : ringKrullDim A < ⊤) :
    Finite (PrimeSpectrum A) := by sorry
