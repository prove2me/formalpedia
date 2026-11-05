-- Prove2me | Theorems.Thm_RotationLadder_Protocol_first_ladder_step
-- name    : RotationLadder.Protocol.first_ladder_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:45.621707+00:00
-- url     : https://prove2.me/theorems/6fed8d1a-48d4-4f48-821b-40a6ebb15ef3
-- title:
--   First ladder step (corrected: normalizer $\sqrt{\cos^4\theta_0+\sin^4\theta_0}$)
-- statement:
--   Put two copies of $|H\rangle=|H_0\rangle$, with $\theta_0=\pi/8$, in the circuit of Fig. 2 and measure the first wire. The unnormalized state of the second wire is
--
--   $$\text{outcome }0:\ \sqrt{\tfrac34}\;|H_1\rangle,\qquad\qquad\text{outcome }1:\ \sqrt{\tfrac14}\;|H_{-1}\rangle,\qquad |H_{-1}\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},$$
--
--   where $\cot\theta_1=\cot^2\theta_0$, and the outcome 0 has probability
--
--   $$p_0=\cos^4\theta_0+\sin^4\theta_0=\frac34 .$$
--
--   This is the step that creates the first new non-stabilizer state from copies of $|H\rangle$.
--
--   Differences from the source:
--   - correction: the post-measurement state is (cos²θ0|0⟩ + sin²θ0|1⟩)/(cos⁴θ0 + sin⁴θ0), and cos θ1|0⟩ + sin θ1|1⟩ = (cos θ0|0⟩ + sin θ0|1⟩)/(cos⁴θ0 + sin⁴θ0) → the normalizer is √(cos⁴θ0 + sin⁴θ0), and the numerator of |H_1⟩ is cos²θ0|0⟩ + sin²θ0|1⟩; reason: at θ0 = π/8 the printed right side has norm 1/(3/4) = 4/3 while the left side is a unit vector; the corrected form gives the paper's own conclusion cot θ1 = cot²θ0
--   - encoding: post-measurement states written normalized, with the probability stated separately → unnormalized post-measurement vectors with explicit amplitudes; reason: the squared norm of each vector is the paper's probability
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 2, Fig. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_RotationLadder_Protocol_cnotSecond
import Definitions.Def_RotationLadder_Protocol_ketH
import Definitions.Def_RotationLadder_Protocol_postOut

namespace RotationLadder.Protocol

/-- **The first step of the ladder (corrected normalization).**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, unnumbered, p. 2.

Two copies of `|H⟩` in Fig. 2 give `√(3/4) |H_1⟩` on outcome `0` and `√(1/4) |H_(-1)⟩` on outcome
`1`, where `|H_(-1)⟩ = (|0⟩ + |1⟩)/√2`; `cot θ_1 = cot² θ_0`; and
`p_0 = cos⁴ θ_0 + sin⁴ θ_0 = 3/4`.

**Formalization Note.** The two displays of p. 2 divide by `cos⁴ θ_0 + sin⁴ θ_0`, which at
`θ_0 = π/8` gives norm `4/3`; the normalizer is the square root of that number. -/
theorem first_ladder_step :
    theta 0 = Real.pi / 8 ∧
      postOut false (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketH 0) (ketH 0))) =
        ((Real.sqrt (3 / 4) : ℝ) : ℂ) • ketH 1 ∧
      postOut true (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketH 0) (ketH 0))) =
        ((Real.sqrt (1 / 4) : ℝ) : ℂ) • ketH (-1) ∧
      ketH (-1) = (WithLp.toLp 2 fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ : EuclideanSpace ℂ Bool) ∧
      Real.cot (theta 1) = Real.cot (theta 0) ^ 2 ∧
      Real.cos (theta 0) ^ 4 + Real.sin (theta 0) ^ 4 = 3 / 4 := by sorry

end RotationLadder.Protocol
