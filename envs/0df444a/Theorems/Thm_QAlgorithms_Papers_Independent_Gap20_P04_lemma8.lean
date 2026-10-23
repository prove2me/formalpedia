-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma8
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:47:38.919139+00:00
-- url     : https://prove2.me/theorems/1b2b0a62-3459-462e-a9c5-96ee46fcca3f
-- title:
--   Lemma-8
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   For any $\lambda\ge0$, suppose $\rho$ maximizes $j-\lambda a$. Then $(j_\rho,a_\rho)$ belongs to the one-use CE region and
--   $$C\le j_\rho\qquad\text{for every }(C,E)\in\mathcal C^{(1)}_{CE}(\mathcal N)
--   \text{ with }E\le a_\rho.$$
--   Thus the optimizer attains the upper classical rate at its budget. This includes $\lambda=0$ and does not require strict Pareto optimality.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 19, Lemma-8

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

/-- PDF p.19, Lemma 8: general one-use CE upper boundary, including lam=0.
At zero weight the proof's strict energy comparison fails; upper C(E) is the
figure-compatible boundary convention, not minimum-E selection among tied optimizers. -/
theorem lemma8 (U : Dilation I B E) (hU : PhysicalDilation U)
    (lam : ℝ) (h0 : 0 ≤ lam) (e : PurifiedInputFamily I) (he : e.Valid)
    (hmax : IsGreatest (purifiedValues (ceScore U lam)) (ceScore U lam e)) :
    CEUpper (oneCE U) (jointInfo U e, inputEntropy e) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
