-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma7
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:46:59.051184+00:00
-- url     : https://prove2.me/theorems/ab4bc523-c8b4-40da-aa48-e946fcee4d1b
-- title:
--   Lemma-7
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   For arbitrary channels $\mathcal N_1,\mathcal N_2$, let $h(\mathcal N)=\max j$ over all physical ensembles. Then
--   $$h(\mathcal N_1\otimes\mathcal N_2)=h(\mathcal N_1)+h(\mathcal N_2).$$
--   The three maxima are attained; the product input domain includes entanglement between the two inputs. No Hadamard assumption is imposed.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 19, Lemma-7

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

/-- PDF p.19, Lemma 7: unrestricted two-channel h additivity, with attainment.
No Hadamard assumption and no copy of the proof's inconsistent B1 subscript. -/
theorem lemma7 (U : Dilation I B E) (V : Dilation J D F)
    (hU : PhysicalDilation U) (hV : PhysicalDilation V) :
    AdditiveMax (purifiedValues (jointInfo U)) (purifiedValues (jointInfo V))
      (purifiedValues (jointInfo (product U V))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
