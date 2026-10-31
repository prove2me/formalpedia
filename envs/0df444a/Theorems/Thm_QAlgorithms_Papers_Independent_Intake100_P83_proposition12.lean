-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_proposition12
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.proposition12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:25:58.496625+00:00
-- url     : https://prove2.me/theorems/2a74c088-a74c-4b40-b294-1ff5c0997b71
-- title:
--   Proposition 12: monotone occurring-charge counts and connected strictness
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $G$ is compact Hausdorff, its group operations are continuous, and all on-site characters are continuous. Let $q_l$ be the number of distinct characters occurring in the actual tensor power $u^{\otimes l}$. For every $l\ge0$,
--
--   $$
--   q_{l+1}\ge q_l.
--   $$
--
--   If $G$ is also connected and $q_1>1$, then $q_{l+1}>q_l$. The tensor power with $l=0$ is the one-dimensional trivial representation, so $q_0=1$.
--
--   This supplies the charge-count monotonicity and the nonscalar connected obstruction without assuming that the original on-site action contains a trivial character.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 20, Proposition 12: monotone occurring charge counts; connected strictness

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.20 Proposition 12: actual occurring-charge counts are monotone, strictly so
for connected compact groups with at least two on-site characters. The l=0 tensor power
is the one-dimensional trivial representation. -/
theorem proposition12 [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [Nonempty A] (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (hcont : ∀ a, Continuous (chi a)) (l : ℕ) :
    chargeCount chi l ≤ chargeCount chi (l + 1) ∧
    (ConnectedSpace G → 1 < chargeCount chi 1 → chargeCount chi l < chargeCount chi (l + 1)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
