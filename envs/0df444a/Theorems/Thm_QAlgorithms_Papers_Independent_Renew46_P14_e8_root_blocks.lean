-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_e8_root_blocks
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.e8_root_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:17:34.14497+00:00
-- url     : https://prove2.me/theorems/f0bf15c0-e2d6-4dba-9e4f-faf81d8c9561
-- title:
--   E8: twenty-seven-root blocks and central E6 frame changes
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   Let $P$ consist of $-k_1\pm k_j$ for $j=4,\ldots,8$, $k_2+k_3$, and
--   $$\tfrac12(-k_1+k_2+k_3+\textstyle\sum_{j=4}^8s_jk_j),\qquad\#\{j:s_j=+1\}\text{ even}.$$
--   Let $z=k_1+k_2+k_3$. Let $C$ consist of $\pm k_i\pm k_j$ for $4\le i<j\le8$ and $\pm\tfrac12(z+\sum_{j=4}^8s_jk_j)$ with an odd number of free positive signs; the outer sign negates the whole vector. Then
--   $$R_{E_8}=A\,\dot\cup\,C\,\dot\cup\,\coprod_{c=1}^3(\rho_cP\,\dot\cup\,-\rho_cP),\quad |P|=27,\ |C|=72,\ |R_{E_8}|=240.$$
--   The unions below are pairwise disjoint. Each cyclic positive block projects to $w_c$, its negative projects to $-w_c$, the central roots project to zero, and $p$ fixes every root in $A$. Moreover $C$ is exactly the image of Table 2's E6 roots under $k'_i\mapsto k_{i+3}$ for $i\le5$, $k'_6\mapsto-z/\sqrt3$. The set $C\cup P\cup(-P)$ is exactly the image of Table 2's E7 roots under $\widetilde k_i\mapsto k_{i+3}$ for $i\le5$, $\widetilde k_6\mapsto k_1$, $\widetilde k_7\mapsto(k_2+k_3)/\sqrt2$.
--
--   This retains both root-system identifications on page 18; Jordan products are the subject of the separate geometry node.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 17, §§4.4.1–4.4.2: Albert pair roots and central E6, (4.6)–(4.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- Albert-block root partition and both frame changes, without asserting Jordan products.
Source: §§4.4.1–4.4.2, (4.6)–(4.7), PDF pp. 17–18. -/
theorem e8_root_blocks :
    rootPartition rootsE8 center8 block8 72 27 ∧
    center8 = rootsE6.image rebaseE6 ∧
    center8 ∪ signed block8 = rootsE7.image rebaseE7 := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
