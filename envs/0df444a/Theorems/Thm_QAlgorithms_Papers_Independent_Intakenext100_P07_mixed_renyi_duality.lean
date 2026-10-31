-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_mixed_renyi_duality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.mixed_renyi_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:16:41.328191+00:00
-- url     : https://prove2.me/theorems/fb5d0930-d472-4be9-8741-20cd2d67bbe7
-- title:
--   5.8
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For a normalized pure ABC state, Hbar_α↑(A|B)+Htilde_β↓(A|C)=0 for reciprocal orders αβ=1, including (0,∞) and (∞,0) interpreted by limits rather than 0*∞ arithmetic.
--
--   $$
--   \overline H_\alpha^\uparrow(A|B)_\rho+\widetilde H_{\alpha^{-1}}^\downarrow(A|C)_\rho=0,\qquad0\le\alpha\le\infty.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 84, 5.8

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

/-- NODE paper:1504.00233#5.8
5.8, arXiv:1504.00233v5, PDF p.84. -/
theorem mixed_renyi_duality [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat ((A × B) × C))
    (hr : IsDensityMatrix r) (hp : paperPure r) (a : ENNReal) :
    conditionalUp false a (traceRight r)+conditionalDown true a⁻¹ (paperTraceMiddle r) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
