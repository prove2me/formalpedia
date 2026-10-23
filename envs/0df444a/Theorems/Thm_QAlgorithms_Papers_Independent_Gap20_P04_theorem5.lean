-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_theorem5
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.theorem5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:44:41.637013+00:00
-- url     : https://prove2.me/theorems/bf60bbd3-ae58-47f7-bbe6-f8d73103d81d
-- title:
--   Theorem-5
-- statement:
--   Let $N\ge1$ be an integer and $\mathcal N_N$ the universal $1\to N$ qubit cloner specified by isometry (12), with the entire $(N+1)$-dimensional symmetric receiver output and $N$-dimensional environment. Put $\Delta_N=N(N+1)/2$, and for $0\le\mu\le1/2$ set $\lambda_i=(N-2i)\mu+i$ for $i=0,\ldots,N$, and $\eta_i=(N-1-2i)\mu+i+1$ for $i=0,\ldots,N-1$. Write $H(v)=-\sum_i v_i\log_2 v_i$, with $0\log_2 0=0$.
--
--   The generating coordinate families are
--   $$F_{CQ}(\mu)=\left(\log_2(N+1)-H(\lambda/\Delta_N),\ H(\lambda/\Delta_N)-H(\eta/\Delta_N)\right),$$
--   $$F_{CE}(\mu)=\left(\log_2(N+1)+H_2(\mu)-H(\eta/\Delta_N),\ H_2(\mu)\right).$$
--   For a family $F(\mu)$, $0\le\mu\le1/2$, let $\mathsf H_{CQ}(F)$ be its closed convex resource-monotone hull: classical and quantum rates can be lowered. Let $\mathsf H_{CE}(F)$ instead allow lowering the classical rate and increasing entanglement consumption, with nonnegative rates in both cases. These hulls include time sharing and endpoint limits.
--
--   They determine exactly
--   $$\mathcal C_{CQ}(\mathcal N_N)=\mathsf H_{CQ}(F_{CQ}),\qquad
--   \mathcal C_{CE}(\mathcal N_N)=\mathsf H_{CE}(F_{CE}).$$
--   This concerns the whole symmetric output, rather than an individual clone.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 12, Theorem-5

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

/-- PDF pp.6,12--15, Theorem 5: the whole symmetric-output cloner, N>=1.
The parent isometry (12) supplies the normalization omitted in the printed complementaryChannel Kraus list. -/
theorem theorem5 (N : ℕ) (hN : 0 < N) :
    capacityCQ (cloningDilation N) = cqHull (cloningCQ N) ∧
      capacityCE (cloningDilation N) = ceHull (cloningCE N) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
