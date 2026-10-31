-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_petz_joint_curvature
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.petz_joint_curvature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:11:04.492294+00:00
-- url     : https://prove2.me/theorems/98572206-3640-4e78-b811-06f625ea1eb3
-- title:
--   4.20
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   Petz trace Qbar_α is jointly concave for 0<α<1 and jointly convex for 1<α≤2.
--
--   $$
--   \overline Q_\alpha(\rho\|\sigma)=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})\text{ is jointly concave for }0<\alpha<1\text{ and jointly convex for }1<\alpha\le2.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 69, 4.20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#4.20
4.20, arXiv:1504.00233v5, PDF p.69. -/
theorem petz_joint_curvature [Nonempty I] (a : ℝ) (r s t u : paperMat I) (hr : r.PosSemidef) (hs : s.PosSemidef)
    (ht : t.PosSemidef) (hu : u.PosSemidef) (l : ℝ) (hl : l ∈ Set.Icc 0 1) :
    (0 < a → a < 1 → l*paperRenyiQ false r s a+(1-l)*paperRenyiQ false t u a ≤ paperRenyiQ false (paperMix l r t) (paperMix l s u) a) ∧
    (1 < a → a ≤ 2 → petzExtendedQ (paperMix l r t) (paperMix l s u) a ≤ (l:EReal)*petzExtendedQ r s a+((1-l:ℝ):EReal)*petzExtendedQ t u a) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
