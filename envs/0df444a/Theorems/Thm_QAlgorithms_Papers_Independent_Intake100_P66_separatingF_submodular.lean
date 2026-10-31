-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_separatingF_submodular
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.separatingF_submodular
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:12:48.952648+00:00
-- url     : https://prove2.me/theorems/3e23e4e7-1f7b-49dc-9b7c-cc3aaf4af63f
-- title:
--   Submodularity of the explicit separating function
-- statement:
--   Fix an integer $n\ge2$, let $N_1=\{x_1,\ldots,x_n\}$ and $N_2=\{a,b,c\}$ be disjoint, and set $N=N_1\sqcup N_2$. For $J\subseteq N_1$ and $K\subseteq N_2$, define
--   $$f(JK)=\theta_K+|J|\lambda_K-\mu_{JK}.$$
--   In the column order $K=(\varnothing,a,b,c,ab,ac,bc,abc)$, the tables are
--   $$\frac{\theta}{n+1}=\bigl(0,2n^3+5n^2,4n^2+2n-1,3n^2+n,2n^3+8n^2+4n-1,2n^3+5n^2+2n,6n^2+4n-1,2n^3+8n^2+4n-1\bigr),$$
--   $$-\lambda=\bigl(n^2,2n^3+5n^2+2n,4n^2+2n-1,4n^2+2n-1,2n^3+8n^2+4n-1,2n^3+5n^2+2n,6n^2+4n-1,2n^3+8n^2+4n-1\bigr).$$
--   The only nonzero $\mu$ values are $\mu_{\{a\}}=2n^2(n+1)$ and $\mu_{\{a,b\}}=2n(n+1)^2$, on those exact subsets of $N$.
--
--   Then $f$ is submodular:
--   $$f(U\cup V)+f(U\cap V)\le f(U)+f(V)\qquad(U,V\subseteq N).$$
--   This supplies a separating set function for the independence argument; monotonicity and entropic realizability are not asserted.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 7, Proposition 3, §IV: submodularity of the explicit function f

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7--8, Proposition 3: the exact table (28)--(32) is submodular. -/
theorem separatingF_submodular (n : ℕ) (hn : 2 ≤ n) :
    IsSubmodular (separatingF n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
