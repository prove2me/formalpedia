-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_classical_oneShot_lp
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.classical_oneShot_lp
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:54:39.11679+00:00
-- url     : https://prove2.me/theorems/7805b18b-e1a6-4cb3-a46e-b7ccc65bbc1a
-- title:
--   Appendix A / LP (69): classical-channel one-shot simulation
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $W(y|x)$ be a finite stochastic channel, with nonempty input and output alphabets, and $\varepsilon\ge0$. Embed it as the quantum map $X\mapsto\sum_{x,y}W(y|x)X_{xx}|y\rangle\langle y|$. Let $t_\varepsilon$ be the infimum of $\sum_yV_y$ over real arrays $Y_{xy},T(y|x),V_y$ satisfying $Y_{xy}\ge T(y|x)-W(y|x)$, $Y_{xy}\ge0$, $T(y|x)\ge0$, $\sum_yT(y|x)=1$, $T(y|x)\le V_y$, and $\sum_yY_{xy}\le\varepsilon$ for every input $x$. Then
--
--   $$S_{\rm NS,\varepsilon}^{(1)}(W)=\log_2\lceil\sqrt{t_\varepsilon}\rceil.$$
--
--   The linear optimum is attained. The resource is quantum communication even though the target is classical.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 18, Appendix A / LP (69): classical-channel one-shot simulation

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

/-- Appendix A, LP (69), PDF p.18: quantum-resource cost for a classical target.
The linear optimum is attained, and every error constraint is per input. -/
theorem classical_oneShot_lp (W : A → B → ℝ) (hW : Stochastic (fun y x => W x y)) (e : ℝ) (he : 0 ≤ e) :
    oneUseSimulationCost .ns (classicalMap W) e = roundedTraceCost (classicalValue W e) ∧
    ∃ Y T : A → B → ℝ, ∃ V : B → ℝ,
      classicalFeasible W e Y T V ∧ (∑ y, V y) = classicalValue W e := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
