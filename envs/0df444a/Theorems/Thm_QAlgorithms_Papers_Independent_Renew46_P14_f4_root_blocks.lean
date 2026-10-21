-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_f4_root_blocks
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.f4_root_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:14:41.327684+00:00
-- url     : https://prove2.me/theorems/2c972617-bfda-4445-bccf-579330718ce1
-- title:
--   F4: six-root blocks and the central scaled A2
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   Set
--   $$\begin{aligned}P={}&\{-k_1,-k_1\pm k_4,\tfrac12(-k_1+k_2+k_3\pm k_4),k_2+k_3\},\\
--   C={}&\{\pm k_4,\ \pm\tfrac12(k_1+k_2+k_3+k_4),\ \pm\tfrac12(k_1+k_2+k_3-k_4)\}.
--   \end{aligned}$$
--   Then
--   $$R_{F_4}=A\,\dot\cup\,C\,\dot\cup\,\coprod_{c=1}^3(\rho_cP\,\dot\cup\,-\rho_cP),\quad |C|=|P|=6,\quad |R_{F_4}|=48.$$
--   The unions below are pairwise disjoint. Each cyclic positive block projects to $w_c$, its negative projects to $-w_c$, the central roots project to zero, and $p$ fixes every root in $A$. With $a=k_4$ and $b=(k_1+k_2+k_3-k_4)/2$, one has $C=\{\pm a,\pm b,\pm(a+b)\}$, $\|a\|^2=\|b\|^2=1$, and $\langle a,b\rangle=-1/2$. Thus this central A2 has scale $1/\sqrt2$ relative to the external roots of squared length two.
--
--   This records the full finite root partition underlying the three pairs.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 9, §§4.1.1–4.1.2: f4 pair roots and central a2, (4.2)–(4.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- F4 six-root blocks, their cyclic opposites, and the central scaled A2.
Source: §§4.1.1–4.1.2, (4.2)–(4.3), PDF pp. 8–9. -/
theorem f4_root_blocks :
    rootPartition rootsF4 center1 block1 6 6 ∧
    isA2 center1 (k 3) ((1 / 2 : ℝ) • (firstThreeSum - k 3)) 1 := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
