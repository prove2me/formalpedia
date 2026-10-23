-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma15
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma15
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:54:33.366229+00:00
-- url     : https://prove2.me/theorems/3b9d473c-9820-4d58-87fc-71c70004028e
-- title:
--   Lemma-15
-- statement:
--   For $0\le\mu\le1/2$, let $e_\mu$ assign probability $1/2$ to each of the unit purifications
--   $$|\psi_0\rangle=\sqrt\mu\,|00\rangle+\sqrt{1-\mu}\,|11\rangle,\qquad
--   |\psi_1\rangle=\sqrt{1-\mu}\,|00\rangle+\sqrt\mu\,|11\rangle.$$
--   Their input marginals are $\operatorname{diag}(\mu,1-\mu)$ and $\operatorname{diag}(1-\mu,\mu)$. For any specified channel, write $\chi,q,j,a$ for the output Holevo information, conditional coherent information, joint mutual information, and conditional reference entropy, in bits.
--
--   For the qubit $p$-dephasing channel, for every $0\le p\le1$,
--   $$\forall\lambda\in[0,1],\quad\exists\mu\in[0,1/2]:\quad
--   j(e_\mu)-\lambda a(e_\mu)=\max_e\{j(e)-\lambda a(e)\}.$$
--   Moreover, the closed convex resource-monotone hull of $(j(e_\mu),a(e_\mu))$ equals the full CE capacity region. Thus one common binary spectrum suffices, including time sharing on constant-slope portions.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 23, Lemma-15

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

/-- PDF p.23, Lemma 15: same binary purifications and common mu for CE generation. -/
theorem lemma15 (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → ∃ mu ∈ Set.Icc (0 : ℝ) (1/2),
      (binaryEnsemble mu).Valid ∧
      IsGreatest (purifiedValues (ceScore (dephasingDilation p) lam))
        (ceScore (dephasingDilation p) lam (binaryEnsemble mu))) ∧
    capacityCE (dephasingDilation p) = ceHull (binaryCE (dephasingDilation p)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
