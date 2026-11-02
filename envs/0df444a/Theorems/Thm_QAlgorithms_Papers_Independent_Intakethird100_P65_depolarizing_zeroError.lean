-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_depolarizing_zeroError
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.depolarizing_zeroError
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:51:07.848928+00:00
-- url     : https://prove2.me/theorems/eec59c51-6b5b-4fdb-a8a0-28656e5aa0bf
-- title:
--   Example 2 / Eqs.(59)–(61): depolarizing zero-error cost
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $d\ge1$ be the dimension of a system and $0\le p\le1$. Extend the depolarizing channel linearly by $\mathcal D_p(X)=(1-p)X+p\operatorname{Tr}(X)I_d/d$. Its regularized zero-error NS simulation cost is
--
--   $$S_{\rm NS,0}(\mathcal D_p)=\tfrac12\log_2(d^2(1-p)+p).$$
--
--   This is not the rounded one-shot cost. It equals $\log_2d$ at $p=0$ and zero at $p=1$ or $d=1$.
--
--   The explicit matrices $V=(d(1-p)+p/d)I$ and $X=\sum_{i,j}|ii\rangle\langle jj|$ satisfy the primal and dual constraints in Eqs.(57),(58), and both objective values equal the independently defined minimum $t_0(\mathcal D_p)$. Thus both displayed witnesses in Eq.(59) are optimal.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 14, Example 2 / Eqs.(59)–(61): depolarizing zero-error cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Example 2, Eqs.(59)--(61), PDF pp.13--14: noise probability p in [0,1],
including d=1. This is the regularized zero-error cost. The explicit primal and
dual optimizers in Eq.(59) are retained with their common optimal objective. -/
theorem depolarizing_zeroError (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    zeroErrorCost (basisDepolarizing A p) =
      Real.logb 2 ((Fintype.card A : ℝ)^2 * (1-p) + p) / 2 ∧
    ZeroErrorWitnessPair (basisDepolarizing A p) (depolarizingPrimalWitness A p)
      (choi (fun X : Mat A => X)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
