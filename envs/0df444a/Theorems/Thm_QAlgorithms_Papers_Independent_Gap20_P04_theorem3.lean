-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_theorem3
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.theorem3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:43:04.621648+00:00
-- url     : https://prove2.me/theorems/e666bb97-a67f-413f-aa7f-a322ff160a42
-- title:
--   Theorem-3
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   Let $\mathcal N$ be Hadamard and $0\le\lambda\le1$. If $\rho$ maximizes $j-\lambda a$, then $(j_\rho,a_\rho)$ lies in the full CE region and
--   $$C\le j_\rho\qquad\text{whenever }(C,E)\in\mathcal C_{CE}(\mathcal N)
--   \text{ and }E\le a_\rho.$$
--   This is the upper classical-rate boundary at that consumption budget, allowing flat portions at $\lambda=0$. It need not select the least consumption among all tied classical-rate optimizers.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 11, Theorem-3

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

/-- PDF pp.11,19--20, Theorem 3: upper C(E), with the flat lam=0 endpoint retained. -/
theorem theorem3 (U : Dilation I B E) (hU : PhysicalDilation U) (hH : Hadamard U)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (e : PurifiedInputFamily I) (he : e.Valid)
    (hmax : IsGreatest (purifiedValues (ceScore U lam)) (ceScore U lam e)) :
    CEUpper (capacityCE U) (jointInfo U e, inputEntropy e) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
