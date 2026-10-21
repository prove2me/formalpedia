-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_e7_root_blocks
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.e7_root_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:16:28.64403+00:00
-- url     : https://prove2.me/theorems/543fc23e-709e-4fd9-9a2f-183a14e2ea08
-- title:
--   E7: the corrected fifteen-root cyclic blocks
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   Let $P$ consist of $-k_1\pm k_j$ for $j=4,5,6$, $k_2+k_3$, and
--   $$\tfrac12(-k_1+k_2+k_3+s_4k_4+s_5k_5+s_6k_6+s_7\sqrt2k_7),\quad(s_4,s_5,s_6)\in\{(---),(-++),(+-+),(++-)\},\ s_7=\pm1.$$
--   Let $C$ consist of $\pm k_i\pm k_j$ for $4\le i<j\le6$, $\pm\sqrt2k_7$, and the whole-vector opposites of $\tfrac12(z+s_4k_4+s_5k_5+s_6k_6+s_7\sqrt2k_7)$ with an odd number of positive signs among $s_4,s_5,s_6$ and free $s_7$, where $z=k_1+k_2+k_3$. Then
--   $$R_{E_7}=A\,\dot\cup\,C\,\dot\cup\,\coprod_{c=1}^3(\rho_cP\,\dot\cup\,-\rho_cP),\qquad |P|=15,\ |C|=30,\ |R_{E_7}|=126.$$
--   The unions below are pairwise disjoint. Each cyclic positive block projects to $w_c$, its negative projects to $-w_c$, the central roots project to zero, and $p$ fixes every root in $A$.
--
--   In Table 2 the even-parity instruction applies to the first six coordinates; the $\sqrt2k_7$ sign is independent. The $(+-+)$ family corrects (4.5) according to the explicit eta sums on page 16.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 15, §4.3.1: fifteen-root block, projection and cyclic opposite pairs, (4.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- Fifteen-root E7 blocks and cyclic opposites; corrected sign/parity scope.
Source: §4.3.1, (4.5), PDF pp. 15–16; eta sums on p. 16 fix the correction. -/
theorem e7_root_blocks : rootPartition rootsE7 center4 block4 30 15 := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
