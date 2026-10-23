-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma1
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:38:04.94096+00:00
-- url     : https://prove2.me/theorems/6a786c7d-1dbd-49df-8e11-54d662f77da1
-- title:
--   Lemma-1
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   Let $h(\mathcal N)=\max j$, with the maximum over the ensembles above. For every integer $n\ge1$,
--   $$h(\mathcal N^{\otimes n})=n\,h(\mathcal N).$$
--   Both maxima are attained; the block maximum permits inputs entangled across uses. This supplies the third-plane bound for arbitrary channels.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 9, Lemma-1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P24
  (Dilation PhysicalDilation ChannelEB Hadamard EqualMax AdditiveMax
   dephasingDilation dephasingGamma cloningDilation)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)

open QAlgorithms.Papers.Independent.Information100.P32 (diagonal)

open QAlgorithms.Papers.Independent.Dependency50.P24 (ensembleHolevoBits)

open QAlgorithms.Papers.Independent.Gap48.P44 (cqTimeSharing ceTimeSharing)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E]

variable [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- PDF pp.9,19, Lemma 1: h is an attained maximum; n>=1. -/
theorem lemma1 (U : Dilation I B E) (hU : PhysicalDilation U) (n : ℕ) (hn : 0 < n) :
    RepeatedMax n (purifiedValues (jointInfo U)) (purifiedValues (jointInfo (dilationPower U n))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
