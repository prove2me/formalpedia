-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_maassen_uffink
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.maassen_uffink
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:56:00.168462+00:00
-- url     : https://prove2.me/theorems/9c7a074f-ca29-4bb3-ac35-02215a446c11
-- title:
--   §7.2 (7.13): Maassen–Uffink relation
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy. In hypothesis testing, $\alpha_n(T;\rho)=\operatorname{Tr}((I-T)\rho^{\otimes n})$ and $\beta_n(T;\sigma)=\operatorname{Tr}(T\sigma^{\otimes n})$, with $0\le T\le I$. The value $\alpha_n^*(u)$ minimizes the first error subject to the second being at most $u$.
--
--   For two ONBs of A, normalized state ρ_A, conjugate orders α,β≥1/2 with 1/α+1/β=2, the actual basis outcome Rényi entropies obey Hα(X)+Hβ(Y)≥−log max_{x,y}|<φx|θy>|².
--
--   $$
--   H_\alpha(X)_{\mathcal M_X(\rho)}+H_\beta(Y)_{\mathcal M_Y(\rho)}\ge-\log_2c,\qquad c=\max_{x,y}|\langle\varphi_x,\vartheta_y\rangle|^2.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 116, §7.2 (7.13): Maassen–Uffink relation

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

/-- NODE paper:1504.00233#7.maassenuffink
§7.2 (7.13): Maassen–Uffink relation, arXiv:1504.00233v5, PDF p.116. -/
theorem maassen_uffink [Nonempty I] (r U V : paperMat I) (hr : IsDensityMatrix r)
    (hU : Uᴴ*U = 1) (hV : Vᴴ*V = 1) (a b : ℝ) (ha : 1/2 ≤ a) (hb : 1/2 ≤ b) (hab : 1/a+1/b = 2) :
    -paperRenyi false (basisLaw U r) 1 (ENNReal.ofReal a)-paperRenyi false (basisLaw V r) 1 (ENNReal.ofReal b) ≥ -paperLogE (basisOverlap U V) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
