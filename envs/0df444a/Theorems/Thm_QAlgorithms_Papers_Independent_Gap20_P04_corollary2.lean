-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_corollary2
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.corollary2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:49:46.854425+00:00
-- url     : https://prove2.me/theorems/f44fbcbe-d0b5-4e7c-8157-f267ba1383ca
-- title:
--   Corollary-2
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   For a Hadamard channel, $0\le\lambda\le1$, and integer $n\ge1$,
--   $$g_\lambda(\mathcal N^{\otimes n})=n g_\lambda(\mathcal N),\qquad
--   \mathcal C_{CE}(\mathcal N)=\mathcal C^{(1)}_{CE}(\mathcal N),$$
--   where $g_\lambda=\max(j-\lambda a)$ and both scalar maxima are attained. This identifies the full CE boundary including flat portions.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 20, Corollary-2

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

/-- PDF p.20, Corollary 2: attained block additivity and full CE single-letterization. -/
theorem corollary2 (U : Dilation I B E) (hU : PhysicalDilation U) (hH : Hadamard U)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (n : ℕ) (hn : 0 < n) :
    RepeatedMax n (purifiedValues (ceScore U lam)) (purifiedValues (ceScore (dilationPower U n) lam)) ∧
      capacityCE U = oneCE U := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
