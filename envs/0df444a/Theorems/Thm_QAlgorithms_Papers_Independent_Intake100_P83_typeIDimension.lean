-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_typeIDimension
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.typeIDimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:14:46.740679+00:00
-- url     : https://prove2.me/theorems/e9822846-04a9-4a82-b60a-b18b2daf5013
-- title:
--   Exact Abelian codimension under semi-universality
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   For topological assertions, assume that the on-site characters are continuous. A finite group has its usual discrete topology; a compact Lie group is finite dimensional, real and Hausdorff.
--
--   Assume $G$ finite or compact Lie, $2\le k\le n$, and semi-universality. Write $q_l$ for the number of occurring $l$-site characters, $r(g)=\operatorname{Tr}u(g)$, and
--
--   $$
--   S_{n,k}=\operatorname{span}_{\mathbb R}\{g\mapsto r(g)^{n-k}f(g): f\text{ occurs on }k\text{ sites}\}.
--   $$
--
--   Using real Lie dimensions of the actual generated groups, one has
--
--   $$
--   \dim\mathcal V_{n,n}-\dim\mathcal V_{n,k}
--   =q_n-\dim_{\mathbb R}S_{n,k}\ge q_n-q_k.
--   $$
--
--   If $G$ is connected, or if $r(g)\ne0$ for every $g$, the final inequality is an equality. The Lie algebra is defined by the actual one-parameter subgroups of $\mathcal V$, and dimension differences are integer differences.
--
--   This separates the exact character-span obstruction from the simpler charge-count bound.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 7, IV C and Appendix A: exact Abelian codimension under semi-universality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.7,18-20 Eqs.(A22)-(A23): exact real character-span codimension under
semi-universality, its charge-count lower bound, and the qualified final equality.
All dimension subtractions are in integers; complete functions on G are spanned over R. -/
theorem typeIDimension [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [Nonempty A] (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (hcont : ∀ a, Continuous (chi a)) (hreg : Finite G ∨ CompactLie G)
    (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (hsemi : SemiUniversal chi n k) :
    (groupDimension (symmetricLocalGroup chi n n) : ℤ) - groupDimension (symmetricLocalGroup chi n k) =
      (chargeCount chi n : ℤ) - Module.finrank ℝ (localChargeSpan chi n k) ∧
    (chargeCount chi n : ℤ) - (chargeCount chi k : ℤ) ≤
      (groupDimension (symmetricLocalGroup chi n n) : ℤ) - groupDimension (symmetricLocalGroup chi n k) ∧
    ((ConnectedSpace G ∨ ∀ g, traceCharacter chi g ≠ 0) →
      (groupDimension (symmetricLocalGroup chi n n) : ℤ) - groupDimension (symmetricLocalGroup chi n k) =
        (chargeCount chi n : ℤ) - chargeCount chi k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
