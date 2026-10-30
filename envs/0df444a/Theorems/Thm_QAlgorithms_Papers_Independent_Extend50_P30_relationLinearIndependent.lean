-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_relationLinearIndependent
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.relationLinearIndependent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:05:50.785187+00:00
-- url     : https://prove2.me/theorems/a44753c2-6678-4f62-bf71-3c373c2ff4bd
-- title:
--   Linear independence in the stable range
-- statement:
--   Let $d$ be prime, $t\geq1$, and $n\geq t-1$. The operators $R(T)=r(T)^{\otimes n}$ indexed by all stochastic Lagrangian subspaces are linearly independent over $\mathbb C$.
--
--   $$
--   \{R(T):T\in\Sigma_{t,t}(d)\}\text{ is linearly independent.}
--   $$
--
--   This gives the source's linear independence in the stable range in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 30, lemma-4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.30, Lemma 4.7: linear independence only in the stated stable range. -/
theorem relationLinearIndependent (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (hn : t - 1 ≤ n) :
    LinearIndependent ℂ (fun T : Lagrangian d t => tensorRelation n T.val) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
