-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_nontorsion_implies_weak_admissibility
-- name    : QAlgorithms.Papers.Independent.Support21.P11.nontorsion_implies_weak_admissibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:57:33.734407+00:00
-- url     : https://prove2.me/theorems/8100bbe9-e3b7-4672-93bc-e144f270af6f
-- title:
--   Nontorsion contraction forces weak admissibility
-- statement:
--   Let $R$ be a commutative unital ring, $\omega_a\in R$ for $a\ge0$, $r\ge1$, $u_1,\ldots,u_r\in R$, and $n\ge2$. In the degenerate cyclotomic BMW algebra $W_{r,n}$, suppose every scalar $c\in R$ satisfying $ce_1=0$ is zero. Define $a_j$ by $\prod_i(z-u_i)=\sum_{j=0}^ra_jz^j$. Then
--
--   $$
--   2\omega_a=\sum_{b=1}^a(-1)^{b-1}\omega_{b-1}\omega_{a-b}-\omega_{a-1}\quad(a\ge1\text{ odd}),
--   \qquad
--   \sum_{j=0}^ra_j\omega_{j+a}=0\quad(a\ge0).
--   $$
--
--   These are exactly the weak admissibility relations. They require neither a domain nor an inverse of $2$.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 3, Corollary 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Corollary 2.4, PDF p.3. Every scalar annihilating e_1 is zero;
no domain or invertibility-of-2 assumption is made. Both recurrences are retained. -/
theorem nontorsion_implies_weak_admissibility (R : Type*) [CommRing R]
    (omega : ℕ → R) (n r : ℕ) (u : Fin r → R) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (he : ∀ c : R, c • cyclotomicE R omega n r u 0 = 0 → c = 0) :
    WeaklyAdmissible omega u := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
