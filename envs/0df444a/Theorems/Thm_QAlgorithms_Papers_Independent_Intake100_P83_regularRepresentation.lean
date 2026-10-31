-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_regularRepresentation
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.regularRepresentation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:14:12.206478+00:00
-- url     : https://prove2.me/theorems/c395f446-e319-46d4-b2e6-0092d26e85c7
-- title:
--   Regular on-site representations are 2-local semi-universal
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $G$ finite, $d=|G|$, and that the on-site representation is unitarily equivalent to left translation on $\mathbb C[G]$. Explicitly, there is a unitary intertwiner $T:\mathbb C[G]\to\mathbb C^A$ with $u(g)T=T L_g$, where $L_g|h\rangle=|gh\rangle$. For $n\ge2$,
--
--   $$
--   l_*=1,\qquad \bigoplus_\mu SU(\mathcal H_\mu)\subseteq\mathcal V_{n,2}.
--   $$
--
--   Here $l_*$ is the least positive length attaining the $n$-site charge count. This specialization achieves a two-site locality bound independently of the order of the group.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 7, IV B, unnumbered: regular on-site representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.3,7: a regular on-site representation has reservoir length one and is 2-local
semi-universal. The intertwiner uses left translation |h> -> |g h>. -/
theorem regularRepresentation [CommGroup G] [Fintype G] [DecidableEq G] [Nonempty A]
    (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (hd : Fintype.card A = Fintype.card G) (hreg : IsRegularOnsiteRepresentation chi)
    (n : ℕ) (hn : 2 ≤ n) :
    reservoirLength chi n = 1 ∧ SemiUniversal chi n 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
