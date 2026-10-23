-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_corollary1
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.corollary1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:42:26.182593+00:00
-- url     : https://prove2.me/theorems/4004ec58-cb5e-4494-8e7e-05547b8bc65f
-- title:
--   Corollary-1
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   For a Hadamard channel, every $\lambda\ge1$ and integer $n\ge1$ satisfy
--   $$f_\lambda(\mathcal N^{\otimes n})=n f_\lambda(\mathcal N),
--   \qquad\mathcal C_{CQ}(\mathcal N)=\mathcal C^{(1)}_{CQ}(\mathcal N),$$
--   where $f_\lambda=\max(\chi+\lambda q)$ and both scalar maxima are attained. This recovers the full CQ trade-off, including convex combinations on flat faces.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 11, Corollary-1

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

/-- PDF p.11, Corollary 1: attained block additivity and full CQ single-letterization. -/
theorem corollary1 (U : Dilation I B E) (hU : PhysicalDilation U) (hH : Hadamard U)
    (lam : ℝ) (hlam : 1 ≤ lam) (n : ℕ) (hn : 0 < n) :
    RepeatedMax n (purifiedValues (cqScore U lam)) (purifiedValues (cqScore (dilationPower U n) lam)) ∧
      capacityCQ U = oneCQ U := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
