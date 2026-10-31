-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_corollary5
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.corollary5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:18:12.795278+00:00
-- url     : https://prove2.me/theorems/2642ebbe-20c0-430b-ad5e-a1771c60d165
-- title:
--   Corollary 5: three gate families synthesize the derived subgroup
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $2\le k\le n$. Fix any family $R$ of invariant Hermitian operators $X(t;t')=|t\rangle\langle t'|+|t'\rangle\langle t|$ on at most $k$ sites. Require that, on $k$ sites, every equal-charge pair of strings is related by a finite product of embeddings of these partial swaps, with identity on all complementary sites. Let $\mathcal F_R$ consist of the following gates on arbitrary named sites: $e^{i\pi|a\rangle\langle a|/2}$, the two-site gates $I-2|ab\rangle\langle ab|$, and $e^{i\theta X(t;t')}$ for $X(t;t')\in R$ and $0\le\theta<2\pi$. Then
--
--   $$
--   [\mathcal V_{n,k},\mathcal V_{n,k}]\subseteq\langle\mathcal F_R\rangle_{\mathrm{finite}}.
--   $$
--
--   The same fixed family $R$ works for every target unitary in this derived subgroup. This gives exact finite synthesis without requiring global transitivity on $n$ sites.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 8, Corollary 5: three families of gates generate the derived subgroup

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.8 Corollary 5 and proof pp.14-15: any fixed qualifying redistribution family
synthesizes the whole derived subgroup by finite products of the three stated gate families. -/
theorem corollary5 [CommGroup G] [Nonempty A] (chi : A → G → ℂ)
    (hchi : IsOnsite chi) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (R : Set (RedistributionTransition A k)) (hR : Redistributes chi k R) :
    derived (symmetricLocalGroup chi n k) ⊆ finiteGateProducts (synthesisFamily R n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
