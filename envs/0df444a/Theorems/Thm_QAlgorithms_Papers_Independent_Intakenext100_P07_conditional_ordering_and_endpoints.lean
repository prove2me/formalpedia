-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_conditional_ordering_and_endpoints
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.conditional_ordering_and_endpoints
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:47:07.72879+00:00
-- url     : https://prove2.me/theorems/7d663e78-322e-4870-9a66-f5d94e993532
-- title:
--   §5.2 (5.20)–(5.27): ordering and special cases
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   Retain up≥down for both families, tilde≥bar for each conditioning convention, and monotonicity in order; trivial conditioning recovers eigenvalue Rényi entropy, order one von Neumann, optimized tilde∞ min-entropy, optimized tilde1/2 max-entropy, tilde2 fixed-reference collision entropy and bar0 optimized Hartley entropy.
--
--   $$
--   \overline H_\alpha^\downarrow\le\overline H_\alpha^\uparrow\le\widetilde H_\alpha^\uparrow,\quad\overline H_\alpha^\downarrow\le\widetilde H_\alpha^\downarrow\le\widetilde H_\alpha^\uparrow,\quad\widetilde H_\infty^\uparrow=H_{\min},\quad\widetilde H_{1/2}^\uparrow=H_{\max}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 77, §5.2 (5.20)–(5.27): ordering and special cases

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

/-- NODE paper:1504.00233#5.ordering
§5.2 (5.20)–(5.27): ordering and special cases, arXiv:1504.00233v5, PDF p.77,78. -/
theorem conditional_ordering_and_endpoints [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r) :
    (∀ a : ENNReal, conditionalDown false a r ≤ conditionalUp false a r ∧
      conditionalDown true a r ≤ conditionalUp true a r ∧ conditionalUp false a r ≤ conditionalUp true a r ∧
      conditionalDown false a r ≤ conditionalDown true a r) ∧
    (∀ sand up : Bool, Antitone (fun a : ENNReal => paperConditional sand up a r)) ∧
    (∀ sand up : Bool, paperConditional sand up 1 r = (conditionalVN r:EReal)) ∧
    conditionalUp true ⊤ r = paperHmin r ∧
    conditionalDown true ⊤ r = sSup {h : EReal | ∃ l : ℝ, h = (l:EReal) ∧
      paperBelow r (((2:ℝ)^(-l):ℂ) • Matrix.kronecker (1:paperMat A) (traceLeft r))} ∧
    conditionalUp true (1/2) r = hmax r ∧
    conditionalDown true 2 r = -paperLogE ((r*Matrix.kronecker (1:paperMat A) (paperPower (traceLeft r) (-1/2))*
      r*Matrix.kronecker (1:paperMat A) (paperPower (traceLeft r) (-1/2))).trace.re) ∧
    conditionalUp false 0 r = hartleyConditional r ∧
    (∀ s : paperMat A, IsDensityMatrix s → ∀ sand up : Bool, ∀ a : ℝ, 0 < a → a ≠ 1 →
      paperConditional sand up (ENNReal.ofReal a) (fun x y : A × Unit => s x.1 y.1) = 
        ((a/(1-a)*Real.logb 2 (paperSchatten s a):ℝ):EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
