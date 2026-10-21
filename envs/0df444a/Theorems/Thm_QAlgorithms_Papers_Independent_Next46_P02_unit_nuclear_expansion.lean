-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_unit_nuclear_expansion
-- name    : QAlgorithms.Papers.Independent.Next46.P02.unit_nuclear_expansion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:33:30.255693+00:00
-- url     : https://prove2.me/theorems/57afff68-4940-4682-82c0-8e18d24eb748
-- title:
--   Unit-vector nuclear expansions with a minimum cost
-- statement:
--   Let $T$ be a bounded endomorphism of a complete real or complex Hilbert space $H$. It is trace-class if and only if there is a finite or countably infinite index set $I\subseteq\mathbb N$, unit vectors $z_k,y_k\in H$ and scalars $\alpha_k\in\mathbb F$ with $\sum_k|\alpha_k|<\infty$ for which, for every $x\in H$, the following series converges in norm:
--
--   $$
--   Tx=\sum_{k\in I}\alpha_k\langle x;z_k\rangle y_k.
--   $$
--
--   When $T$ is trace-class, its trace norm is both the infimum and an attained minimum of the costs of all these representations:
--
--   $$
--   \|T\|_1=\inf\sum_{k\in I}|\alpha_k|=\min\sum_{k\in I}|\alpha_k|.
--   $$
--
--   The empty representation of zero is allowed. This retains attainment without requiring a unit vector in the zero Hilbert space or requiring both vector families to lie in an invariant kernel complement.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 18, §6, unnumbered unit-vector characterization and minimum cost

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF p.18: the unit-vector characterization, the infimum formula, AND its
attainment as a minimum. No ker(T)-perp invariance or infinite unit sequence is assumed. -/
theorem unit_nuclear_expansion (T : H →L[F] H) :
    (IsModulusTraceClass T ↔ ∃ (s : Set ℕ) (z y : s → H) (a : s → F),
      UnitNuclearRepresentation T s z y a) ∧
    (IsModulusTraceClass T → IsLeast (unitExpansionCosts T) (modulusTraceNorm T) ∧
      modulusTraceNorm T = sInf (unitExpansionCosts T)) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
