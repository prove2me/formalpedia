-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma13
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:52:55.229105+00:00
-- url     : https://prove2.me/theorems/cd2bc7c6-63b1-432f-9b04-512f1b4d9416
-- title:
--   Lemma-13
-- statement:
--   For $0\le\mu\le1/2$, let $e_\mu$ assign probability $1/2$ to each of the unit purifications
--   $$|\psi_0\rangle=\sqrt\mu\,|00\rangle+\sqrt{1-\mu}\,|11\rangle,\qquad
--   |\psi_1\rangle=\sqrt{1-\mu}\,|00\rangle+\sqrt\mu\,|11\rangle.$$
--   Their input marginals are $\operatorname{diag}(\mu,1-\mu)$ and $\operatorname{diag}(1-\mu,\mu)$. For any specified channel, write $\chi,q,j,a$ for the output Holevo information, conditional coherent information, joint mutual information, and conditional reference entropy, in bits.
--
--   For the qubit $p$-dephasing channel, for every $0\le p\le1$,
--   $$\forall\lambda\ge1,\quad\exists\mu\in[0,1/2]:\quad
--   \chi(e_\mu)+\lambda q(e_\mu)=\max_e\{\chi(e)+\lambda q(e)\}.$$
--   Moreover, the closed convex resource-monotone hull of $(\chi(e_\mu),q(e_\mu))$ equals the full CQ capacity region. Thus one common binary spectrum suffices, including time sharing on constant-slope portions.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 21, Lemma-13

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

/-- PDF pp.21--22, Lemma 13: purified binary ensemble attains CQ maxima and generates
all CQ trade-offs for p-dephasing, including both endpoint channels. -/
theorem lemma13 (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (∀ lam : ℝ, 1 ≤ lam → ∃ mu ∈ Set.Icc (0 : ℝ) (1/2),
      (binaryEnsemble mu).Valid ∧
      IsGreatest (purifiedValues (cqScore (dephasingDilation p) lam))
        (cqScore (dephasingDilation p) lam (binaryEnsemble mu))) ∧
    capacityCQ (dephasingDilation p) = cqHull (binaryCQ (dephasingDilation p)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
