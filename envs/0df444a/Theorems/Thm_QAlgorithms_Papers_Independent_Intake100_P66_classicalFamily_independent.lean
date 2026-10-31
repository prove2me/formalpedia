-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_classicalFamily_independent
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.classicalFamily_independent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:14:58.793139+00:00
-- url     : https://prove2.me/theorems/57ec7a45-6fca-46ff-bd28-94b7e52097ec
-- title:
--   Independence of the classical Makarychev family
-- statement:
--   Fix an integer $n\ge2$ and the ground set $N=\{a,b,c,x_1,\ldots,x_n\}$. The target is the standard singleton instance of $C_n$, with zero constraints $Z_1=I_h(a:c\mid b)$ and $Z_2=I_h(b:c\mid a)$. For pairwise disjoint subsets $U,V,W,\alpha_1,\ldots,\alpha_p$ of a fixed finite ground set, empty subsets permitted, put
--   $$L_p(h;U,V,W,\alpha)=\sum_{i=1}^p I_h(U:V\mid\alpha_i)+\sum_{i=1}^p h(\alpha_i)-h\!\left(\bigcup_{i=1}^p\alpha_i\right)-(p-1)I_h(UV:W).$$
--   Here $h$ is a normalized real set function, $I_h(U:V)=h(U)+h(V)-h(UV)$ and $I_h(U:V\mid W)=h(UW)+h(VW)-h(W)-h(UVW)$; juxtaposition denotes union. The constrained inequality $C_p$ is $L_p\ge0$ under $I_h(U:W\mid V)=I_h(V:W\mid U)=0$.
--    An eligible constrained instance has every nontrivial constraint equal, as an entropy coefficient form, to one of $Z_1,Z_2$; an identically zero form adds no constraint. Equality of forms is understood on normalized set functions, so the empty entropy coordinate is zero. No purification transformation or closure operation is included.
--   Let $\mathcal A_n^{\mathrm{cl}}$ contain every strong-subadditivity instance and every monotonicity form $h(V)-h(U)$ with $U\subseteq V\subseteq N$, together with every eligible $C_p$ instance for $p\ge2$, $p\ne n$. Then no finite coefficient identity exists of the form
--   $$L_n(h;a,b,c,(\{x_i\}))=\sum_{j=1}^k w_j L_j(h)+r_1Z_1(h)+r_2Z_2(h),\qquad w_j\ge0,\quad L_j\in\mathcal A_n^{\mathrm{cl}},\quad r_1,r_2\in\mathbb R.$$
--   This is independence from the classical basic inequalities and the other family members, not the existence of a violating joint probability distribution.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 9, §IV, unnumbered: independence of the classical Makarychev family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Section IV: classical independence. Monotonicity replaces weak
monotonicity in the basic generators; no violating probability law is asserted. -/
theorem classicalFamily_independent (n : ℕ) (hn : 2 ≤ n) :
    ¬ Derivable {L | ClassicalBasic L ∨ OtherFamily n L}
      (constraints n) (standardFamily n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
