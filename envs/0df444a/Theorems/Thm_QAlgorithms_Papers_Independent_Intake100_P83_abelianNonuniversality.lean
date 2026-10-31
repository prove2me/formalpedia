-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_abelianNonuniversality
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.abelianNonuniversality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:15:48.11961+00:00
-- url     : https://prove2.me/theorems/9406a63c-19cb-4913-b034-b191caef4d9e
-- title:
--   Connected nonscalar and trace-zero obstructions to universality
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   For topological assertions, assume that the on-site characters are continuous. A finite group has its usual discrete topology; a compact Lie group is finite dimensional, real and Hausdorff.
--
--   Assume $G$ finite or compact Lie, and $1\le k<n$. Suppose either $G$ is connected and the on-site representation has at least two inequivalent characters, or $\operatorname{Tr}u(g_0)=0$ for some $g_0\in G$. Then
--
--   $$
--   \mathcal V_{n,k}\ne\mathcal V_{n,n}.
--   $$
--
--   No semi-universality assumption is required. The connected clause explicitly excludes scalar on-site actions; the trace-zero clause already excludes them.
--
--   This identifies two physical sources of unavoidable locality constraints on general symmetric unitaries.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 7, IV C, unnumbered: connected and trace-zero nonuniversality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.7,19-20: connected nonscalar and trace-zero obstructions to universality.
No semi-universality hypothesis is imposed. A scalar on-site representation is excluded
only in the connected clause. -/
theorem abelianNonuniversality [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [Nonempty A] (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (hcont : ∀ a, Continuous (chi a)) (hreg : Finite G ∨ CompactLie G)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (hobstruction : (ConnectedSpace G ∧ 1 < chargeCount chi 1) ∨
      ∃ g, traceCharacter chi g = 0) :
    symmetricLocalGroup chi n k ≠ symmetricLocalGroup chi n n := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
