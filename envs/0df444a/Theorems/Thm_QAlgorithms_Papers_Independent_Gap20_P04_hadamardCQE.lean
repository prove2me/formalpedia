-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_hadamardCQE
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.hadamardCQE
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:35:57.364513+00:00
-- url     : https://prove2.me/theorems/16f81c7d-b6b9-4ecf-9759-fe5b115f1c15
-- title:
--   Unnumbered main result: Hadamard CQE single-letterization
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   If the complementary channel is entanglement-breaking, then
--   $$\mathcal C_{CQE}(\mathcal N)=\mathcal C^{(1)}_{CQE}(\mathcal N).$$
--   Here a single common ensemble must satisfy all three constraints $C+2Q\le j$, $Q\le q+E$, and $C+Q\le\chi+q+E$. This identifies the full positive-consumption capacity region by one channel use.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 1, Unnumbered main result: Hadamard CQE single-letterization

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

/-- PDF pp.1,9,11,16: Hadamard CQE single-letterization, consumption convention. -/
theorem hadamardCQE (U : Dilation I B E) (hU : PhysicalDilation U) (hH : Hadamard U) :
    capacityCQE U = oneCQE U := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
