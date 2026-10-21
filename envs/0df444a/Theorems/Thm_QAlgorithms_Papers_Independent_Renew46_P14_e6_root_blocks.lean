-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_e6_root_blocks
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.e6_root_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:15:23.633063+00:00
-- url     : https://prove2.me/theorems/e5f41522-74cd-4298-93ee-b87ca2e06fdd
-- title:
--   E6: nine-root blocks and two central A2 systems
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   Write $z=k_1+k_2+k_3$. Let $P$ consist of $-k_1\pm k_4$, $-k_1\pm k_5$, $k_2+k_3$, and
--   $$\tfrac12(-k_1+k_2+k_3+s_4k_4+s_5k_5+s_6\sqrt3k_6),\quad(s_4,s_5,s_6)\in\{(+,-,-),(+,+,+),(-,+,-),(-,-,+)\}.$$
--   Define $C_1=\{\pm a,\pm b,\pm(a+b)\}$ with $a=k_4+k_5$, $b=(z-k_4-k_5-\sqrt3k_6)/2$, and $C_2$ by the same formula with $a=k_4-k_5$, $b=(z-k_4+k_5+\sqrt3k_6)/2$. Set $C=C_1\cup C_2$. Then
--   $$R_{E_6}=A\,\dot\cup\,C\,\dot\cup\,\coprod_{c=1}^3(\rho_cP\,\dot\cup\,-\rho_cP),\quad |P|=9,\ |C|=12,\ |R_{E_6}|=72.$$
--   The unions below are pairwise disjoint. Each cyclic positive block projects to $w_c$, its negative projects to $-w_c$, the central roots project to zero, and $p$ fixes every root in $A$. In each $C_i$ the two displayed simple roots have squared length two and inner product $-1$. Every root of $C_1$ is orthogonal to every root of $C_2$.
--
--   These are precisely the two central A2 root systems and the six nine-root blocks.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 11, §§4.2.1–4.2.2: nine-root blocks and central a2+a2, (4.4)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- E6 nine-root blocks and its two orthogonal central A2 root systems.
Source: §§4.2.1–4.2.2, (4.4), PDF p. 11. -/
theorem e6_root_blocks :
    rootPartition rootsE6 center2 block2 12 9 ∧
    isA2 center2First (k 3 + k 4)
      ((1 / 2 : ℝ) • (firstThreeSum - k 3 - k 4 - Real.sqrt (3 : ℝ) • k 5)) 2 ∧
    isA2 center2Second (k 3 - k 4)
      ((1 / 2 : ℝ) • (firstThreeSum - k 3 + k 4 + Real.sqrt (3 : ℝ) • k 5)) 2 ∧
    (∀ x ∈ center2First, ∀ y ∈ center2Second, dotProduct x y = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
