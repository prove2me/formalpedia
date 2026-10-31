-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_corollary4
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.corollary4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:12:24.875656+00:00
-- url     : https://prove2.me/theorems/25561ea1-b2f3-4acf-8062-d123a04a88be
-- title:
--   Corollary 4: finite Abelian semi-universality with corrected locality bound
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   If $G$ is finite and $\max(|G|,2)\le k\le n$, then
--
--   $$
--   \bigoplus_\mu SU(\mathcal H_\mu)\subseteq\mathcal V_{n,k}.
--   $$
--
--   This provides a locality bound independent of system size for every fixed finite Abelian symmetry. The printed $\min(|G|,2)$ is corrected to $\max(|G|,2)$, following the proof and the p.3 announcement; the printed quotation is retained verbatim.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 7, Corollary 4: finite Abelian semi-universality (printed bound corrected)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.3,7, Corollary 4, corrected printed bound.
Printed: k >= min(|G|,2). Changed: k >= max(|G|,2), as required by the reservoir
proof on p.7 and the introduction on p.3. With Z_3, n=3, k=2 the printed bound
fails: 000 and 111 have equal charge but no weight-changing local transition.
Independent moderation of this source correction remains required. -/
theorem corollary4 [CommGroup G] [Fintype G] [Nonempty A] (chi : A → G → ℂ)
    (hchi : IsOnsite chi) (n k : ℕ) (hk : max (Fintype.card G) 2 ≤ k) (hkn : k ≤ n) :
    SemiUniversal chi n k := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
