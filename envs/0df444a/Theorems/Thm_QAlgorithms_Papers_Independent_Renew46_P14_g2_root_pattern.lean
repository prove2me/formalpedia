-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_g2_root_pattern
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.g2_root_pattern
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:14:07.721998+00:00
-- url     : https://prove2.me/theorems/a98977a9-6e1e-4041-ac17-76e95bcda259
-- title:
--   G2: the external A2 hexagon and two weight triangles
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   The twelve roots satisfy
--   $$R_{G_2}=A\,\dot\cup\,\{w_1,w_2,w_3\}\,\dot\cup\,\{-w_1,-w_2,-w_3\},\qquad |A|=6.$$
--   The three $w_c$ are distinct, sum to zero, and satisfy $w_i-w_j=k_j-k_i$ and $\langle w_i,w_j\rangle=2/3$ for $i=j$ and $-1/3$ otherwise. All twelve roots lie in $\Pi$.
--
--   These are the oriented standard and dual weight triangles of the prototype diagram; no Albert-algebra assertion is made.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 5, §4 opening, Fig. 2: the g2 prototype

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- G2 prototype: external A2 and the oriented standard/dual weight triangles.
Source: §4 opening, Table 2 and Fig. 2, PDF pp. 5–6. -/
theorem g2_root_pattern :
    rootsG2.card = 12 ∧ external.card = 6 ∧
    (Finset.univ.image externalWeight).card = 3 ∧
    Disjoint external (signed (Finset.univ.image externalWeight)) ∧
    Disjoint (Finset.univ.image externalWeight) ((Finset.univ.image externalWeight).image (fun x => -x)) ∧
    (∑ i : Fin 3, externalWeight i) = 0 ∧
    (∀ i j : Fin 3, externalWeight i - externalWeight j = k ⟨j.val, by omega⟩ - k ⟨i.val, by omega⟩) ∧
    (∀ i j : Fin 3, dotProduct (externalWeight i) (externalWeight j) = if i = j then 2 / 3 else -1 / 3) ∧
    (∀ x ∈ rootsG2, rootProjection x = x) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
