-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P06_cyclotomic_hecke_normal_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P06.cyclotomic_hecke_normal_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:48:24.427337+00:00
-- url     : https://prove2.me/theorems/6dfb8395-e57c-4612-84c0-7832f9862ff4
-- title:
--   The specified cyclotomic Hecke basis
-- statement:
--   Let $S$ be any commutative unital ring, let $q,u_1,\ldots,u_r$ be units of $S$, and let $n,r\ge1$. Let $H_{n,S,r}(q^2;u_1,\ldots,u_r)$ be the quotient of the affine Hecke algebra by $\prod_{i=1}^r(x_1-u_i)=0$. Define $x'_j=g_{j-1}\cdots g_1x_1g_1^{-1}\cdots g_{j-1}^{-1}$, and define $T_\alpha$ using inverse generators in a reduced expression for $\alpha\in\mathfrak S_n$. The specified quotient-image family
--   $$\Sigma'_r=\bigl(T_\alpha(x'_n)^{a_n}\cdots(x'_1)^{a_1}\bigr)_{\alpha\in\mathfrak S_n,\ 0\le a_j<r}$$
--   is an $S$-basis of the cyclotomic Hecke algebra. Its index set has $r^n n!$ elements.
--
--   This gives freeness with the particular normal-form words over arbitrary rings, including the zero ring, without distinct-root, domain, or admissibility assumptions. A literal positive module-rank equality is not asserted over the zero ring.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, PDF p. 44, Corollary 6.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Corollary 6.11, PDF pp.44--45: the specified bounded-word family is a basis
for arbitrary commutative S and unit parameters, including the zero ring. -/
theorem cyclotomic_hecke_normal_basis (S : Type*) [CommRing S] (q : Sˣ)
    (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : 0 < r) (u : Fin r → Sˣ) :
    ∃ b : Module.Basis (Equiv.Perm (Fin n) × (Fin n → Fin r)) S
        (CyclotomicHecke S q n r u),
      ∀ d, b d = boundedHeckeNormalWord S q n r u d := by sorry

end QAlgorithms.Papers.Independent.Intake100.P06

end
