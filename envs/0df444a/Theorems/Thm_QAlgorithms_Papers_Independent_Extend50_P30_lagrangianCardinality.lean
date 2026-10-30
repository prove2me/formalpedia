-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_lagrangianCardinality
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.lagrangianCardinality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:07:19.191787+00:00
-- url     : https://prove2.me/theorems/6c6b0d10-7cec-4a38-a158-1b29f6f90291
-- title:
--   Number of stochastic Lagrangians
-- statement:
--   Let $d$ be prime and $t\geq1$. Let $\Sigma_{t,t}(d)$ denote the dimension-$t$, totally isotropic subspaces for $q(x,y)=x\cdot x-y\cdot y$ modulo $D$, containing the all-ones vector. Their number is the product below; the empty product equals one.
--
--   $$
--   |\Sigma_{t,t}(d)|=\prod_{k=0}^{t-2}(d^k+1).
--   $$
--
--   This gives the source's number of stochastic lagrangians in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 33, theorem-4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.33, Theorem 4.10: the product is empty for t=1. -/
theorem lagrangianCardinality (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t) :
    Nat.card (Lagrangian d t) = commutantCount d t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
