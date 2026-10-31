-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_quantumFamily_independent
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.quantumFamily_independent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:14:21.92961+00:00
-- url     : https://prove2.me/theorems/33f8800d-e57c-4ac1-89d2-388812891aba
-- title:
--   Mutual independence of the quantum constrained family
-- statement:
--   Fix an integer $n\ge2$ and the ground set $N=\{a,b,c,x_1,\ldots,x_n\}$. The target is the standard singleton instance of $C_n$, with zero constraints $Z_1=I_h(a:c\mid b)$ and $Z_2=I_h(b:c\mid a)$. For pairwise disjoint subsets $U,V,W,\alpha_1,\ldots,\alpha_p$ of a fixed finite ground set, empty subsets permitted, put
--   $$L_p(h;U,V,W,\alpha)=\sum_{i=1}^p I_h(U:V\mid\alpha_i)+\sum_{i=1}^p h(\alpha_i)-h\!\left(\bigcup_{i=1}^p\alpha_i\right)-(p-1)I_h(UV:W).$$
--   Here $h$ is a normalized real set function, $I_h(U:V)=h(U)+h(V)-h(UV)$ and $I_h(U:V\mid W)=h(UW)+h(VW)-h(W)-h(UVW)$; juxtaposition denotes union. The constrained inequality $C_p$ is $L_p\ge0$ under $I_h(U:W\mid V)=I_h(V:W\mid U)=0$.
--    An eligible constrained instance has every nontrivial constraint equal, as an entropy coefficient form, to one of $Z_1,Z_2$; an identically zero form adds no constraint. Equality of forms is understood on normalized set functions, so the empty entropy coordinate is zero. No purification transformation or closure operation is included.
--   Let $\mathcal A_n^{\mathrm q}$ consist of every strong-subadditivity or weak-monotonicity instance on disjoint subsets of $N$, together with every eligible instance of $C_p$ for $p\ge2$, $p\ne n$. Then there is no finite coefficient identity
--   $$L_n(h;a,b,c,(\{x_i\}))=\sum_{j=1}^k w_j L_j(h)+r_1Z_1(h)+r_2Z_2(h),\qquad w_j\ge0,\quad L_j\in\mathcal A_n^{\mathrm q},\quad r_1,r_2\in\mathbb R.$$
--   This states independence in the source's finite linear-combination sense, using abstract normalized set functions; it does not assert a quantum state violating a valid entropy inequality.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 6, §IV, unnumbered: mutual independence of the quantum constrained inequalities

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3,6--9, Section IV: finite linear independence with matching constraints.
All basic quantum instances are allowed; the witness need not be entropic. -/
theorem quantumFamily_independent (n : ℕ) (hn : 2 ≤ n) :
    ¬ Derivable {L | QuantumBasic L ∨ OtherFamily n L}
      (constraints n) (standardFamily n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
