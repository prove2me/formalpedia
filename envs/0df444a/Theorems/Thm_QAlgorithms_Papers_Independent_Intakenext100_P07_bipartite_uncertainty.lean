-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_bipartite_uncertainty
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.bipartite_uncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:56:33.494981+00:00
-- url     : https://prove2.me/theorems/80d0605b-8468-4594-91d1-86dbb639f429
-- title:
--   §7.2 (7.23)–(7.24): bipartite uncertainty relation
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy. In hypothesis testing, $\alpha_n(T;\rho)=\operatorname{Tr}((I-T)\rho^{\otimes n})$ and $\beta_n(T;\sigma)=\operatorname{Tr}(T\sigma^{\otimes n})$, with $0\le T\le I$. The value $\alpha_n^*(u)$ minimizes the first error subject to the second being at most $u$.
--
--   Let rho_AB be normalized, and let two orthonormal-basis measurements on A have maximum squared overlap c. Let alpha,beta,gamma>=1/2 be finite, different from one, with gamma/(gamma-1)=alpha/(alpha-1)+beta/(beta-1) and (alpha-1)(beta-1)(gamma-1)<0. Then the displayed bipartite uncertainty relation holds for the actual measured marginals.
--
--   $$
--   \widetilde H_\alpha^\uparrow(X|B)_{\mathcal M_X(\rho)}+\widetilde H_\beta^\uparrow(Y|B)_{\mathcal M_Y(\rho)}\ge\widetilde H_\gamma^\uparrow(A|B)_\rho-\log_2c.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 117, §7.2 (7.23)–(7.24): bipartite uncertainty relation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#7.bipartite
§7.2 (7.23)–(7.24): bipartite uncertainty relation, arXiv:1504.00233v5, PDF p.117,118. -/
theorem bipartite_uncertainty [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (U V : paperMat A) (hU : Uᴴ*U = 1) (hV : Vᴴ*V = 1) (a b c : ℝ)
    (ha : 1/2 ≤ a) (hb : 1/2 ≤ b) (hc : 1/2 ≤ c) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1)
    (hrel : c/(c-1) = a/(a-1)+b/(b-1)) (hsign : (a-1)*(b-1)*(c-1) < 0) :
    conditionalUp true (ENNReal.ofReal c) r-paperLogE (basisOverlap U V) ≤ conditionalUp true (ENNReal.ofReal a) (paperBasisMeasurement U r)+
      conditionalUp true (ENNReal.ofReal b) (paperBasisMeasurement V r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
