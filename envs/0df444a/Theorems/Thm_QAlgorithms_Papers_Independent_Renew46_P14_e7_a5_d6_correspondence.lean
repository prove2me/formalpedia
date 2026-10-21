-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_e7_a5_d6_correspondence
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.e7_a5_d6_correspondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:16:57.00069+00:00
-- url     : https://prove2.me/theorems/574251dc-3a88-4262-bc92-7c3f805ef1ba
-- title:
--   E7: the explicit A5–D6 eta correspondence
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   Define
--   $$\begin{aligned}
--   \eta_1&=(-k_1-k_4-k_5-k_6)/2,&\eta_2&=(-k_1-k_4+k_5+k_6)/2,\\
--   \eta_3&=(-k_1+k_4-k_5+k_6)/2,&\eta_4&=(-k_1+k_4+k_5-k_6)/2,\\
--   \eta_5&=(k_2+k_3+\sqrt2k_7)/2,&\eta_6&=(k_2+k_3-\sqrt2k_7)/2.
--   \end{aligned}$$
--   The six vectors are orthonormal. If $C$ is the thirty-root central set of §4.3.2 and $P$ the corrected fifteen-root block (4.5), then
--   $$C=\{\eta_i-\eta_j:i\ne j\},\qquad P=\{\eta_i+\eta_j:i<j\},\qquad C\cup P\cup(-P)=\{\pm\eta_i\pm\eta_j:i<j\}.$$
--   The respective cardinalities are $30$, $15$, and $60$.
--
--   This identifies the central A5 and full D6 root systems by the paper's concrete frame, rather than assuming the identification.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 15, §4.3.2: the thirty central A5 roots and the D6 root correspondence

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- The displayed orthonormal eta frame identifies the central A5 and the full D6.
Source: §4.3.2, PDF pp. 15–16. Differences are ordered; sums use i<j. -/
theorem e7_a5_d6_correspondence :
    (∀ i j : Fin 6, dotProduct (d6Frame i) (d6Frame j) = if i = j then 1 else 0) ∧
    center4 = etaDifferences ∧ block4 = etaSums ∧
    center4.card = 30 ∧ etaSums.card = 15 ∧
    center4 ∪ signed block4 = etaD6 ∧ etaD6.card = 60 := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
