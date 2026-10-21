-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_e8_explicit_nested_root_partition
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.e8_explicit_nested_root_partition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:18:12.191675+00:00
-- url     : https://prove2.me/theorems/91052678-e2bc-4a71-ba5a-8be08735d784
-- title:
--   E8: the explicit four-A2 and six-pair root partition
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   Put $z=k_1+k_2+k_3$ and $h=k_4+k_5+k_6$. For $c=1,2,3$, let $Q_c$ consist of $-k_c\pm k_j$ ($4\le j\le8$), $z-k_c$, and $-k_c+(z+\sum_{j=4}^8s_jk_j)/2$ with an even number of positive free signs. For $f=4,5,6$, let $T_f$ consist of $-k_f\pm k_7$, $-k_f\pm k_8$, $h-k_f$, and
--   $$-k_f+\tfrac12(sz+h+s_7k_7+s_8k_8),$$
--   retaining exactly the four choices $s,s_7,s_8\in\{\pm1\}$ that belong to the even-parity E8 root set after expanding all eight coefficients. Let $A_c=A$, $A_f=\{k_i-k_j:4\le i\ne j\le6\}$, and
--   $$\begin{aligned}
--   A_{g1}&=\{\pm(k_7+k_8),\ \pm(z+h-k_7-k_8)/2,\ \pm(z+h+k_7+k_8)/2\},\\
--   A_{g2}&=\{\pm(k_7-k_8),\ \pm(-z+h-k_7+k_8)/2,\ \pm(-z+h+k_7-k_8)/2\}.
--   \end{aligned}$$
--   Then the following union is disjoint:
--   $$R_{E_8}=A_c\dot\cup A_f\dot\cup A_{g1}\dot\cup A_{g2}\dot\cup\coprod_{c=1}^3(Q_c\dot\cup(-Q_c))\dot\cup\coprod_{f=4}^6(T_f\dot\cup(-T_f)).$$
--   Each A2 set has six roots of squared length two, with simple-root inner product $-1$, and different A2 sets are orthogonal. Each $Q_c$ has 27 roots and is exactly $\{x\in R_{E_8}:p(x)=w_c\}$. Each $T_f$ has nine roots and is contained in the central E6 set (4.7). Hence $|R_{E_8}|=4\cdot6+3\cdot54+3\cdot18=240$.
--
--   The particle names are labels for this mathematical partition and assert no physical prediction.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 21, §6, unnumbered mathematical root list underlying the color/family notation

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- Mathematical root partition underlying the color/family labels; no physics claim.
Source: §6 explicit lists, PDF p. 21. The lepton signs use expanded E8 parity. -/
theorem e8_explicit_nested_root_partition :
    rootsE8 = Finset.univ.biUnion nestedPiece ∧ rootsE8.card = 240 ∧
    (∀ i j : NestedPiece, i ≠ j → Disjoint (nestedPiece i) (nestedPiece j)) ∧
    (∀ a : Fin 4, (nestedA2 a).card = 6) ∧
    (∀ c b, (orientedBlock block8 c b).card = 27) ∧
    (∀ f : Fin 3, (innerBlock f).card = 9 ∧ innerBlock f ⊆ center8) ∧
    (∀ a b : Fin 4, a ≠ b → ∀ x ∈ nestedA2 a, ∀ y ∈ nestedA2 b, dotProduct x y = 0) ∧
    (∀ a : Fin 4, ∃ x y : V, isA2 (nestedA2 a) x y 2) ∧
    (∀ c : Fin 3, rootsE8.filter (fun x => rootProjection x = externalWeight c) =
      orientedBlock block8 c true) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
