-- Prove2me | Theorems.Thm_ValuationSubring_ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc
-- name    : ValuationSubring.ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/5a64d881-41ae-5af5-82f6-e622f9545454
-- title:
--   Krull dimension of a residue valuation ring between two primes
-- statement:
--   Let $L$ be a field, let $A$ be a valuation subring of $L$, and let $Q \subseteq P$ be prime ideals of $A$. Since $Q \le P$, the associated coarsenings satisfy $A_P \le A_Q$, where $A_{\mathfrak p}$ denotes `A.ofPrime` $\mathfrak p$, the valuation subring of $L$ obtained by localising $A$ at $\mathfrak p$. Inside the residue field of the local ring $A_Q$ one forms `residueValuationSubring`, namely the image of $A_P$ under the composite of the inclusion $A_P \hookrightarrow A_Q$ with the residue map of $A_Q$; the definition records that this image, being a subring satisfying the valuation condition that for every element of the residue field either it or its inverse lies in the image, is a valuation subring of $\mathrm{Res}(A_Q)$. The assertion is that the ring Krull dimension of this valuation subring equals the order-theoretic Krull dimension of the closed interval $[\,Q, P\,]$ in the prime spectrum of $A$, i.e. of the subposet of primes $\mathfrak p$ of $A$ with $Q \subseteq \mathfrak p \subseteq P$; both sides are taken in `WithBot ℕ∞`.
--
--   This is the standard comparison, in the theory of coarsenings of a valuation, between the rank of the residue valuation ring attached to a pair of comparable primes of a valuation ring and the length of the chains of primes lying between them; in particular the residue valuation ring has rank one exactly when $Q \subsetneq P$ are consecutive. It is used in the study of regular prolongations on algebraic curves, where a finite Krull dimension hypothesis is converted into information about residue maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc.lean

import Mathlib
import Definitions.Def_ValuationSubring_ResidueValuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc
    {L : Type*} [Field L] (A : ValuationSubring L) (Q P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (hQP : Q ≤ P) :
    ringKrullDim ((A.ofPrime P).residueValuationSubring (A.ofPrime Q)
        (ValuationSubring.ofPrime_le_of_le A Q P hQP)) =
      Order.krullDim (Set.Icc (⟨Q, inferInstance⟩ : PrimeSpectrum A) ⟨P, inferInstance⟩) := by sorry
