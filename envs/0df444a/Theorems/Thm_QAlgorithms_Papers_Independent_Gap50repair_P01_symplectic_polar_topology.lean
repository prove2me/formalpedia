-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_symplectic_polar_topology
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.symplectic_polar_topology
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:14:56.29044+00:00
-- url     : https://prove2.me/theorems/34dbacd0-974d-45b3-8d07-427386e02a3a
-- title:
--   Theorem 7
-- statement:
--   Let $n\ge1$. Every $A\in\operatorname{Sp}(2n,\mathbb R)$ has a unique factorization $A=OP$, where $O$ is orthogonal and symplectic, and $P$ is symmetric, positive definite and symplectic, with $P^2=A^\mathsf TA$. There is a unique symmetric $S$ in the symplectic Lie algebra such that
--
--   $$e^S=A^\mathsf TA,\qquad P=e^{S/2},\qquad S^\mathsf T\Omega_0+\Omega_0S=0.$$
--
--   Moreover $A\leftrightarrow(O,S)$ is a homeomorphism between the symplectic group and $U(n)$ times that vector space of symmetric Lie algebra matrices, with inverse $(O,S)\mapsto Oe^{S/2}$. This includes the exponential and topology clauses as well as the polar factors.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 6, Theorem 7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Theorem 7, PDF pp.6–7: unique polar factors, logarithm, and product homeomorphism. -/
theorem symplectic_polar_topology {n : ℕ} (hn : 1 ≤ n) :
    (∀ A : GroupedRealMatrix n, IsSymplectic A →
      (∃! OP : GroupedRealMatrix n × GroupedRealMatrix n, A = OP.1*OP.2 ∧ IsOrthogonal OP.1 ∧ IsSymplectic OP.1 ∧
        OP.2.transpose = OP.2 ∧ OP.2.PosDef ∧ IsSymplectic OP.2 ∧ OP.2*OP.2 = A.transpose*A) ∧
      (∃! S : GroupedRealMatrix n, IsSymmetricLie S ∧ NormedSpace.exp S = A.transpose*A ∧
        polarP A = NormedSpace.exp ((1/2 : ℝ) • S))) ∧
    (∃ h : SymplecticSpace n ≃ₜ (UnitarySpace n × SymmetricLieSpace n),
      ∀ A, A.val = (h A).1.val*NormedSpace.exp ((1/2 : ℝ) • (h A).2.val)) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
