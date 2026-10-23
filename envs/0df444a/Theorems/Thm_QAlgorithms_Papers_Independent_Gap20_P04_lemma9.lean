-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma9
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:48:25.050072+00:00
-- url     : https://prove2.me/theorems/a6f394fb-8a33-4794-b594-957e2d659cdc
-- title:
--   Lemma-9
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   For every $\lambda>1$,
--   $$\max_\rho(j_\rho-\lambda a_\rho)
--   =\max_{\text{pure conditional input ensembles}}\chi.$$
--   Both maxima are attained, and the right side is the one-use Holevo optimum. Weights above one are therefore redundant for the nontrivial CE support trade-off.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 19, Lemma-9

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

/-- PDF pp.19--20, Lemma 9: superunit CE weight gives the one-use Holevo maximum. -/
theorem lemma9 (U : Dilation I B E) (hU : PhysicalDilation U)
    (lam : ℝ) (h1 : 1 < lam) :
    EqualMax (purifiedValues (ceScore U lam)) (holevoValues U) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
