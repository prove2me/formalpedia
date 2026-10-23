-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma5
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:45:24.714183+00:00
-- url     : https://prove2.me/theorems/d298947a-bf54-46c6-97a6-df6d74a23b69
-- title:
--   Lemma-5
-- statement:
--   For $0\le\mu\le1/2$, let $e_\mu$ assign probability $1/2$ to each of the unit purifications
--   $$|\psi_0\rangle=\sqrt\mu\,|00\rangle+\sqrt{1-\mu}\,|11\rangle,\qquad
--   |\psi_1\rangle=\sqrt{1-\mu}\,|00\rangle+\sqrt\mu\,|11\rangle.$$
--   Their input marginals are $\operatorname{diag}(\mu,1-\mu)$ and $\operatorname{diag}(1-\mu,\mu)$. For any specified channel, write $\chi,q,j,a$ for the output Holevo information, conditional coherent information, joint mutual information, and conditional reference entropy, in bits.
--
--   For the universal symmetric-output $1\to N$ cloner, for every integer $N\ge1$,
--   $$\forall\lambda\ge1,\quad\exists\mu\in[0,1/2]:\quad
--   \chi(e_\mu)+\lambda q(e_\mu)=\max_e\{\chi(e)+\lambda q(e)\}.$$
--   Moreover, the closed convex resource-monotone hull of $(\chi(e_\mu),q(e_\mu))$ equals the full CQ capacity region. Thus one common binary spectrum suffices, including time sharing on constant-slope portions.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 12, Lemma-5

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

/-- PDF pp.12--13, Lemma 5: a common binary purified input both attains support optima
and generates the full CQ region; its spectrum is optimized, not assumed optimal. -/
theorem lemma5 (N : ℕ) (hN : 0 < N) :
    (∀ lam : ℝ, 1 ≤ lam → ∃ mu ∈ Set.Icc (0 : ℝ) (1/2),
      (binaryEnsemble mu).Valid ∧
      IsGreatest (purifiedValues (cqScore (cloningDilation N) lam))
        (cqScore (cloningDilation N) lam (binaryEnsemble mu))) ∧
    capacityCQ (cloningDilation N) = cqHull (binaryCQ (cloningDilation N)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
