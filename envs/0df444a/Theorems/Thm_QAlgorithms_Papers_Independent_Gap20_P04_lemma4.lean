-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma4
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:41:41.411005+00:00
-- url     : https://prove2.me/theorems/293ca41c-63c8-4910-9088-790af635e161
-- title:
--   Lemma-4
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   For $\lambda\ge1$, define $f_\lambda(\mathcal N)=\max_\rho(\chi_\rho+\lambda q_\rho)$. If $\mathcal N_1$ is Hadamard and $\mathcal N_2$ is any CPTP channel on nonzero finite registers, then
--   $$f_\lambda(\mathcal N_1\otimes\mathcal N_2)
--   =f_\lambda(\mathcal N_1)+f_\lambda(\mathcal N_2).$$
--   All three maxima are attained, and the product optimization includes entangled inputs. This is strong two-channel additivity.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 10, Lemma-4

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

/-- PDF pp.10--11, Lemma 4: strong additivity, second channel arbitrary, lam>=1. -/
theorem lemma4 (U : Dilation I B E) (V : Dilation J D F)
    (hU : PhysicalDilation U) (hV : PhysicalDilation V) (hH : Hadamard U)
    (lam : ℝ) (hlam : 1 ≤ lam) :
    AdditiveMax (purifiedValues (cqScore U lam)) (purifiedValues (cqScore V lam))
      (purifiedValues (cqScore (product U V) lam)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
