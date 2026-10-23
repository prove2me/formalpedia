-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_theorem1
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.theorem1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:37:08.963817+00:00
-- url     : https://prove2.me/theorems/a957c88e-96ff-42f0-b7c0-d55a3c51885b
-- title:
--   Theorem-1
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   If both two-resource capacity regions equal their one-use ensemble unions, then
--   $$\mathcal C_{CQ}(\mathcal N)=\mathcal C^{(1)}_{CQ}(\mathcal N),\quad
--   \mathcal C_{CE}(\mathcal N)=\mathcal C^{(1)}_{CE}(\mathcal N)
--   \quad\Longrightarrow\quad
--   \mathcal C_{CQE}(\mathcal N)=\mathcal C^{(1)}_{CQE}(\mathcal N).$$
--   The three-dimensional union uses all of (17)–(19) for the same ensemble. The result reduces full CQE single-letterization to the CQ and CE trade-offs.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 9, Theorem-1

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

/-- PDF pp.8--9, Theorem 1: both two-resource regions suffice; all three planes remain. -/
theorem theorem1 (U : Dilation I B E) (hU : PhysicalDilation U)
    (hCQ : capacityCQ U = oneCQ U) (hCE : capacityCE U = oneCE U) :
    capacityCQE U = oneCQE U := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
