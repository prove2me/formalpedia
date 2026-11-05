-- Prove2me | Theorems.Thm_RotationLadder_Protocol_ladder_step
-- name    : RotationLadder.Protocol.ladder_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:35.464761+00:00
-- url     : https://prove2.me/theorems/902918a0-e832-43bb-96a0-0f6ecb573c06
-- title:
--   Fig. 2 moves $|H_i\rangle$ to $|H_{i+1}\rangle$ or $|H_{i-1}\rangle$
-- statement:
--   For every level $i\ge0$, put $|H_0\rangle|H_i\rangle$ in the circuit of Fig. 2 and measure the first wire. The unnormalized state of the second wire is
--
--   $$\text{outcome }0:\ \sqrt{p_{0,i}}\;|H_{i+1}\rangle,\qquad\qquad\text{outcome }1:\ \sqrt{1-p_{0,i}}\;|H_{i-1}\rangle,$$
--
--   with $p_{0,i}=\cos^2\theta_i\cos^2\theta_0+\sin^2\theta_i\sin^2\theta_0$. Moreover $\cot\theta_i=\cot^{\,i+1}\theta_0$ for every integer $i$.
--
--   So one copy of $|H\rangle$ moves the state one level up or down the ladder.
--
--   Differences from the source:
--   - encoding: post-measurement states written normalized, with the probability stated separately → unnormalized post-measurement vectors with explicit amplitudes; reason: the squared norm of each vector is the paper's probability
--   - generalization: cot θ_i = cot^{i+1} θ0 for the levels of the ladder → the identity for every integer i; reason: specializes to the levels i ≥ −1 that the paper uses
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, pp. 2-3, Fig. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_RotationLadder_Protocol_cnotSecond
import Definitions.Def_RotationLadder_Protocol_ketH
import Definitions.Def_RotationLadder_Protocol_ladderProb
import Definitions.Def_RotationLadder_Protocol_postOut

namespace RotationLadder.Protocol

/-- **The ladder step of Fig. 2.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, unnumbered, pp. 2-3.

`|H_0⟩|H_i⟩` in Fig. 2 gives `√(p_(0,i)) |H_(i+1)⟩` on outcome `0` and `√(1 - p_(0,i)) |H_(i-1)⟩` on
outcome `1`, and `cot θ_i = cot^(i+1) θ_0` for every integer `i`.

**Formalization Note.** The vectors are the unnormalized post-measurement states, so their squared
norms are the outcome probabilities. -/
theorem ladder_step :
    (∀ i : ℤ, Real.cot (theta i) = Real.cot (theta 0) ^ (i + 1)) ∧
    (∀ i : ℕ,
      postOut false (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketH 0) (ketH i))) =
          ((Real.sqrt (ladderProb i) : ℝ) : ℂ) • ketH ((i : ℤ) + 1) ∧
      postOut true (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketH 0) (ketH i))) =
          ((Real.sqrt (1 - ladderProb i) : ℝ) : ℂ) • ketH ((i : ℤ) - 1)) := by sorry

end RotationLadder.Protocol
