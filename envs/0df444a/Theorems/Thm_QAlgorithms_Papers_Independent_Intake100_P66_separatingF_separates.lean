-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_separatingF_separates
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.separatingF_separates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:13:30.772183+00:00
-- url     : https://prove2.me/theorems/b73c96b3-cb76-4eac-8634-97d29d84a58d
-- title:
--   The explicit function separates the standard family member
-- statement:
--   Fix an integer $n\ge2$, let $N_1=\{x_1,\ldots,x_n\}$ and $N_2=\{a,b,c\}$ be disjoint, and set $N=N_1\sqcup N_2$. For $J\subseteq N_1$ and $K\subseteq N_2$, define
--   $$f(JK)=\theta_K+|J|\lambda_K-\mu_{JK}.$$
--   In the column order $K=(\varnothing,a,b,c,ab,ac,bc,abc)$, the tables are
--   $$\frac{\theta}{n+1}=\bigl(0,2n^3+5n^2,4n^2+2n-1,3n^2+n,2n^3+8n^2+4n-1,2n^3+5n^2+2n,6n^2+4n-1,2n^3+8n^2+4n-1\bigr),$$
--   $$-\lambda=\bigl(n^2,2n^3+5n^2+2n,4n^2+2n-1,4n^2+2n-1,2n^3+8n^2+4n-1,2n^3+5n^2+2n,6n^2+4n-1,2n^3+8n^2+4n-1\bigr).$$
--   The only nonzero $\mu$ values are $\mu_{\{a\}}=2n^2(n+1)$ and $\mu_{\{a,b\}}=2n(n+1)^2$, on those exact subsets of $N$.
--
--   For pairwise disjoint subsets $U,V,W,\alpha_1,\ldots,\alpha_p$ of a fixed finite ground set, empty subsets permitted, put
--   $$L_p(h;U,V,W,\alpha)=\sum_{i=1}^p I_h(U:V\mid\alpha_i)+\sum_{i=1}^p h(\alpha_i)-h\!\left(\bigcup_{i=1}^p\alpha_i\right)-(p-1)I_h(UV:W).$$
--   Here $h$ is a normalized real set function, $I_h(U:V)=h(U)+h(V)-h(UV)$ and $I_h(U:V\mid W)=h(UW)+h(VW)-h(W)-h(UVW)$; juxtaposition denotes union. The constrained inequality $C_p$ is $L_p\ge0$ under $I_h(U:W\mid V)=I_h(V:W\mid U)=0$.
--
--   The function satisfies $I_f(a:c\mid b)=I_f(b:c\mid a)=0$. For every integer $p\ge2$ with $p\ne n$ and every pairwise disjoint family $\alpha_i\subseteq N_1$,
--   $$L_p(f;a,b,c,\alpha)\ge0,\qquad L_n(f;a,b,c,(\{x_i\})_{i=1}^n)<0.$$
--   The labels $a,b,c$ are fixed in the first assertion and the $\alpha_i$ may be empty. This is a separation by the explicit table, without requiring $f$ to obey weak monotonicity.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 8, Proposition 4, §IV: the explicit f separates C_n from the other C_p

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8--9, Proposition 4: fixed a,b,c and disjoint X-subsets, including empty
ones; all other p>=2 families hold, but the standard C_n residual is negative. -/
theorem separatingF_separates (n : ℕ) (hn : 2 ≤ n) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (separatingF n) = 0 ∧
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (separatingF n) = 0 ∧
    (∀ (p : ℕ), 2 ≤ p → p ≠ n → ∀ alpha : Fin p → Finset (entropyParty n),
      (∀ i, alpha i ⊆ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t)) →
      (∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) →
      0 ≤ evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n)) ∧
    evaluateEntropyForm (standardFamily n) (separatingF n) < 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
