-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_up_duality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_up_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:15:08.395986+00:00
-- url     : https://prove2.me/theorems/9b97bbb4-a241-470f-a43b-0e1d38440eee
-- title:
--   5.7
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For a normalized pure ABC state, Htilde_α↑(A|B)+Htilde_β↑(A|C)=0 for 1/α+1/β=2, α,β∈[1/2,∞], including complementary endpoint (1/2,∞).
--
--   $$
--   \widetilde H_\alpha^\uparrow(A|B)_\rho+\widetilde H_\beta^\uparrow(A|C)_\rho=0,\qquad\alpha^{-1}+\beta^{-1}=2.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 82, 5.7

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

/-- NODE paper:1504.00233#5.7
5.7, arXiv:1504.00233v5, PDF p.82. -/
theorem sandwiched_up_duality [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat ((A × B) × C))
    (hr : IsDensityMatrix r) (hp : paperPure r) (a b : ENNReal) (ha : 1/2 ≤ a) (hb : 1/2 ≤ b) (hab : a⁻¹+b⁻¹ = 2) :
    conditionalUp true a (traceRight r)+conditionalUp true b (paperTraceMiddle r) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
