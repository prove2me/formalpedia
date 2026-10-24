-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_cq_block_formula
-- name    : QAlgorithms.Papers.Independent.Support50.P19.cq_block_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:32:56.367142+00:00
-- url     : https://prove2.me/theorems/71aa3ff1-44d2-4043-91a6-0194bad8d8d9
-- title:
--   Explicit block formula for ensemble alpha-Holevo information
-- statement:
--   Let $\alpha>1$ and let $\{p_x,\rho_x\}$ be a finite ensemble of density operators on a nonzero finite complex space, allowing zero probabilities. Define $\rho_{XQ}=\sum_xp_x|x\rangle\langle x|\otimes\rho_x$ and $\rho_X=\sum_xp_x|x\rangle\langle x|$. Then
--   $$\widetilde\chi_\alpha(\{p_x,\rho_x\}):=\min_\sigma\widetilde D_\alpha(\rho_{XQ}\Vert\rho_X\otimes\sigma)=\min_\sigma\frac1{\alpha-1}\log_2\sum_xp_x\widetilde Q_\alpha(\rho_x\Vert\sigma).$$
--   Both minima range over density operators and are attained. The alpha power is inside each trace defining $\widetilde Q_\alpha$. A zero-weight unsupported block contributes zero. This formula computes the ensemble information from its conditional states.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 17, eq14

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)

open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)

open QAlgorithms.Papers.Independent.Information100.P56 (sandwichedTrace)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Claimed50.P26
  (CovariantIrreducible minOutput UnassistedExponentialConverse)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/-- PDF p.17, (14): the cq definition equals the explicit support-aware block formula. -/
theorem cq_block_formula [Nonempty I] (a : ℝ) (ha : 1 < a) (e : Ensemble I) :
    renyiEnsembleInformation true a e.prob e.state = blockInformation a e.prob e.state ∧
    ∃ sigma : {X : Matrix I I ℂ // IsDensityMatrix X}, blockInformation a e.prob e.state =
      ((1 / (a - 1) : ℝ) : EReal) *
        elogNN (∑ x, ENNReal.ofReal (e.prob x) * sandwichedTrace a (e.state x) sigma.1) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
