-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma3
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:40:06.360672+00:00
-- url     : https://prove2.me/theorems/45c08304-b3b4-471f-bdcd-5555d14143e4
-- title:
--   Lemma-3
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   For every $0\le\lambda<1$,
--   $$\max_\rho(\chi_\rho+\lambda q_\rho)
--   =\max_{\text{pure conditional input ensembles}}\chi.$$
--   Both maxima are attained. The right side is the one-use Holevo optimum. This makes weights below one redundant for the nontrivial CQ support trade-off; it does not assert that every zero-weight optimizer has nonnegative coherent information.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 10, Lemma-3

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

/-- PDF p.10, Lemma 3: subunit weights give the attained one-use Holevo maximum. -/
theorem lemma3 (U : Dilation I B E) (hU : PhysicalDilation U)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    EqualMax (purifiedValues (cqScore U lam)) (holevoValues U) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
