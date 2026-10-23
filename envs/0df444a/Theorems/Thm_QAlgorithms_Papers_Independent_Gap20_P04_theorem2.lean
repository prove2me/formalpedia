-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_theorem2
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.theorem2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:39:17.602114+00:00
-- url     : https://prove2.me/theorems/51df4369-b6c3-4298-b9a8-76fda35b4573
-- title:
--   Theorem-2
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   Suppose $\mathcal N$ is Hadamard, $\lambda\ge1$, and a physical ensemble $\rho$ maximizes $\chi+\lambda q$. Then its pair $(\chi_\rho,q_\rho)$ belongs to the full CQ capacity region and
--   $$C+\lambda Q\le\chi_\rho+\lambda q_\rho\qquad
--   \text{for every }(C,Q)\in\mathcal C_{CQ}(\mathcal N).$$
--   Thus every such optimizer gives a supporting trade-off point; support ties are retained.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 9, Theorem-2

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

/-- PDF pp.9--11, Theorem 2: Hadamard is standing in Section IV; all support ties allowed. -/
theorem theorem2 (U : Dilation I B E) (hU : PhysicalDilation U) (hH : Hadamard U)
    (lam : ℝ) (hlam : 1 ≤ lam) (e : PurifiedInputFamily I) (he : e.Valid)
    (hmax : IsGreatest (purifiedValues (cqScore U lam)) (cqScore U lam e)) :
    CQSupport (capacityCQ U) lam (ensembleHolevoBits e.prob (fun x => receiverChannel U (e.input x)), ensembleCoherentBits U e) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
