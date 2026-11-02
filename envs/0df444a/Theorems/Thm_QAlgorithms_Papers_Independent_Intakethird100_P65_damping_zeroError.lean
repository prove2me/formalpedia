-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_damping_zeroError
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.damping_zeroError
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:51:50.946906+00:00
-- url     : https://prove2.me/theorems/b82e328b-92e3-44c2-b9d5-6bda1a8d65cb
-- title:
--   Example 3 / Eqs.(62),(63): amplitude-damping zero-error cost
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   For $0\le r\le1$, let $\mathcal N_r$ be the qubit channel with Kraus matrices $E_0=|0\rangle\langle0|+\sqrt{1-r}|1\rangle\langle1|$ and $E_1=\sqrt r|0\rangle\langle1|$. Then
--
--   $$S_{\rm NS,0}(\mathcal N_r)=\tfrac12\log_2\bigl(2(1+\sqrt{1-r})-r\bigr).$$
--
--   The subtraction of $r$ is outside the factor two. The regularized zero-error cost is one qubit at $r=0$ and zero at $r=1$.
--
--   The matrices $V=(1+\sqrt{1-r})|0\rangle\langle0|+(\sqrt{1-r}+1-r)|1\rangle\langle1|$ and $X=(|00\rangle+|11\rangle)(\langle00|+\langle11|)$ satisfy the primal and dual constraints in Eqs.(57),(58), and both objective values equal the independently defined minimum $t_0(\mathcal N_r)$. Thus the displayed witnesses in Eq.(62) are optimal.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 14, Example 3 / Eqs.(62),(63): amplitude-damping zero-error cost

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

/-- Example 3, Eqs.(62)--(63), PDF p.14: -r is outside the factor 2.
The displayed primal optimizer and unnormalized plus-Bell dual optimizer are
feasible and attain the independently defined zero-error trace optimum. -/
theorem damping_zeroError (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    zeroErrorCost (damping r) = Real.logb 2 (2*(1 + Real.sqrt (1-r)) - r) / 2 ∧
    ZeroErrorWitnessPair (damping r) (dampingPrimalWitness r)
      (choi (fun X : Mat Bool => X)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
