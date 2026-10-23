-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_theorem4
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.theorem4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:43:46.852305+00:00
-- url     : https://prove2.me/theorems/9472614c-97fb-481f-a6ae-748dbf478285
-- title:
--   Theorem-4
-- statement:
--   Let $0\le p\le1$ and let $\mathcal N_p(\sigma)=(1-p)\sigma+p\Delta(\sigma)$ be the qubit dephasing channel, where $\Delta$ removes off-diagonal matrix entries. Write $H_2$ for binary entropy in bits and
--   $$\gamma(\mu,p)=\frac12+\frac12\sqrt{1-16\frac p2\left(1-\frac p2\right)\mu(1-\mu)}.$$
--   For $0\le\mu\le1/2$, define
--   $$F_{CQ}(\mu)=(1-H_2(\mu),\ H_2(\mu)-H_2(\gamma(\mu,p))),$$
--   $$F_{CE}(\mu)=(1+H_2(\mu)-H_2(\gamma(\mu,p)),\ H_2(\mu)).$$
--   For a family $F(\mu)$, $0\le\mu\le1/2$, let $\mathsf H_{CQ}(F)$ be its closed convex resource-monotone hull: classical and quantum rates can be lowered. Let $\mathsf H_{CE}(F)$ instead allow lowering the classical rate and increasing entanglement consumption, with nonnegative rates in both cases. These hulls include time sharing and endpoint limits.
--
--   Then
--   $$\mathcal C_{CQ}(\mathcal N_p)=\mathsf H_{CQ}(F_{CQ}),\qquad
--   \mathcal C_{CE}(\mathcal N_p)=\mathsf H_{CE}(F_{CE}).$$
--   These are exact generating families for both trade-offs, retaining the degenerate flat portions at $p=0,1$.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 12, Theorem-4

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

/-- PDF pp.12,21--24, Theorem 4: the displayed families generate exactly both regions.
The endpoint flats are retained through resource-monotone hulls, not strict Pareto tests. -/
theorem theorem4 (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    capacityCQ (dephasingDilation p) = cqHull (dephasingCQ p) ∧
      capacityCE (dephasingDilation p) = ceHull (dephasingCE p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
