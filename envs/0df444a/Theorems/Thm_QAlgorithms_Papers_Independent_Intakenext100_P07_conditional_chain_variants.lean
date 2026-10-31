-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_conditional_chain_variants
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.conditional_chain_variants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:49:08.945296+00:00
-- url     : https://prove2.me/theorems/1fdd333c-c13c-41fc-91a0-b80f6a85d33f
-- title:
--   §5.4 (5.81)–(5.84): further conditional chain rules
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For normalized ABC: Hbarα↑(AB|C)≤Hbar0↑(A|BC)+Hbarα↑(B|C); Htildeα↑(AB|C)≥Htildeα↓(A|BC)+Hmin(B|C); replacing the down entropy gives (5.84) with α=2−1/β and admissible positive orders.
--
--   $$
--   \overline H_\alpha^\uparrow(AB|C)\le\overline H_0^\uparrow(A|BC)+\overline H_\alpha^\uparrow(B|C),\quad\widetilde H_\alpha^\uparrow(AB|C)\ge\widetilde H_\alpha^\downarrow(A|BC)+H_{\min}(B|C)\ge\widetilde H_\beta^\uparrow(A|BC)+H_{\min}(B|C),\quad\alpha=2-1/\beta.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 87, §5.4 (5.81)–(5.84): further conditional chain rules

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

/-- NODE paper:1504.00233#5.chainvariants
Equations (5.81), (5.83), (5.84), PDF p.87. Each clause has its own order domain. -/
theorem conditional_chain_variants [Nonempty A] [Nonempty B] [Nonempty C]
    (r : paperMat ((A × B) × C)) (hr : IsDensityMatrix r) :
    (∀ a : ENNReal, a ≤ 2 → conditionalUp false a r ≤ conditionalUp false 0 (paperRegroup r)+conditionalUp false a (paperMarginalBC r)) ∧
    (∀ a : ENNReal, 1/2 ≤ a → conditionalDown true a (paperRegroup r)+conditionalUp true ⊤ (paperMarginalBC r) ≤ conditionalUp true a r) ∧
    (∀ a b : ENNReal, 1/2 ≤ a → 1/2 ≤ b → a = transformedOrder b →
      conditionalUp true b (paperRegroup r)+conditionalUp true ⊤ (paperMarginalBC r) ≤ conditionalUp true a r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
