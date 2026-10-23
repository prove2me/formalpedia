-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma10
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:49:02.950375+00:00
-- url     : https://prove2.me/theorems/1fea72de-bdc8-49d2-a724-b3bf6da34472
-- title:
--   Lemma-10
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   Put $g_\lambda(\mathcal N)=\max_\rho(j_\rho-\lambda a_\rho)$. If $\mathcal N_1$ is Hadamard, $\mathcal N_2$ is arbitrary CPTP, and $0\le\lambda\le1$, then
--   $$g_\lambda(\mathcal N_1\otimes\mathcal N_2)
--   =g_\lambda(\mathcal N_1)+g_\lambda(\mathcal N_2).$$
--   All maxima are attained over the full pure-ensemble domain. This is strong additivity, with no Hadamard restriction on the second channel.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 20, Lemma-10

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

/-- PDF p.20, Lemma 10: strong CE additivity, second channel arbitrary, 0<=lam<=1. -/
theorem lemma10 (U : Dilation I B E) (V : Dilation J D F)
    (hU : PhysicalDilation U) (hV : PhysicalDilation V) (hH : Hadamard U)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    AdditiveMax (purifiedValues (ceScore U lam)) (purifiedValues (ceScore V lam))
      (purifiedValues (ceScore (product U V) lam)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
