-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_stabilizerMomentFormula
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.stabilizerMomentFormula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:21:26.108657+00:00
-- url     : https://prove2.me/theorems/90308570-8e6b-48d5-bc5b-25c6bea0aeee
-- title:
--   All stabilizer moments
-- statement:
--   Let $d$ be prime and $n,t\geq1$. Average uniformly over the finite set of pure stabilizer density matrices, counting each global-phase class once. The resulting moment is the sum of all stochastic Lagrangian relation tensors divided by its trace normalization. This holds also for $n<t-1$.
--
--   $$
--   \mathbb E_S(S^{\otimes t})=\frac1{Z_{n,d,t}}\sum_{T\in\Sigma_{t,t}(d)}R(T),\qquad Z_{n,d,t}=d^n\prod_{k=0}^{t-2}(d^k+d^n).
--   $$
--
--   This gives the source's all stabilizer moments in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 46, theorem-5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.46, Theorem 5.3: all positive n,t, with no stable-range hypothesis. -/
theorem stabilizerMomentFormula (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (hn : 1 ≤ n) (ht : 1 ≤ t) :
    stabilizerMoment d n t = (momentNormalization d n t : ℂ)⁻¹ •
      ∑ T : Lagrangian d t, tensorRelation n T.val := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
