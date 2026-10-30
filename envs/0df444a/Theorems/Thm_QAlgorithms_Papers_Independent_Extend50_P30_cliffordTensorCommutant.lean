-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_cliffordTensorCommutant
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.cliffordTensorCommutant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:54:55.169999+00:00
-- url     : https://prove2.me/theorems/033ede30-8d05-4d6d-9512-21e62bf4e5b0
-- title:
--   Commutant of Clifford tensor powers
-- statement:
--   Let $d$ be prime, $t\geq1$, and $n\geq t-1$. Let $\Sigma_{t,t}(d)$ be the stochastic Lagrangian subspaces for the source quadratic form modulo $D$, and let $R(T)=r(T)^{\otimes n}$, with $r(T)=\sum_{(x,y)\in T}|x\rangle\langle y|$. Then these operators are linearly independent over $\mathbb C$ and span exactly the operators commuting with every $U^{\otimes t}$ for $U\in\mathrm{Cliff}(n,d)$.
--
--   $$
--   |\Sigma_{t,t}(d)|=\prod_{k=0}^{t-2}(d^k+1),\qquad\operatorname{span}_{\mathbb C}\{R(T):T\in\Sigma_{t,t}(d)\}=\operatorname{Comm}(\mathrm{Cliff}(n,d)^{\otimes t}).
--   $$
--
--   This gives the source's commutant of clifford tensor powers in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 28, theorem-4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.28, Theorem 4.3: exact commutant basis, cardinality, and stable range. -/
theorem cliffordTensorCommutant (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (hn : t - 1 ≤ n) :
    Nat.card (Lagrangian d t) = commutantCount d t ∧
    LinearIndependent ℂ (fun T : Lagrangian d t => tensorRelation n T.val) ∧
    Submodule.span ℂ (Set.range (fun T : Lagrangian d t => tensorRelation n T.val)) =
      cliffordCommutant d n t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
