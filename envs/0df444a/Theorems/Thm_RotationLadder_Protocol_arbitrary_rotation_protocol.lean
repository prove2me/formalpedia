-- Prove2me | Theorems.Thm_RotationLadder_Protocol_arbitrary_rotation_protocol
-- name    : RotationLadder.Protocol.arbitrary_rotation_protocol
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:07.468695+00:00
-- url     : https://prove2.me/theorems/b7cd3fb5-7887-405c-8187-b166c536d6dd
-- title:
--   Copies of $|H\rangle$ implement every single-qubit unitary to any accuracy, almost surely, at finite expected cost
-- statement:
--   Copies of $|H\rangle$, Clifford gates and measurements implement every single-qubit unitary to every accuracy. Precisely:
--
--   1. **Ladder step.** For $i\ge0$, Fig. 2 on $|H_0\rangle|H_i\rangle$ leaves $\sqrt{p_{0,i}}\,|H_{i+1}\rangle$ on outcome 0 and $\sqrt{1-p_{0,i}}\,|H_{i-1}\rangle$ on outcome 1.
--   2. **Bounds.** For $i\ge0$, $\tfrac34\le p_{0,i}<\cos^2(\pi/8)$ and $0<\theta_i<\pi/4$.
--   3. **Rotation with the resource.** For $i\ge0$, $XHS|H_i\rangle=|Z(2\theta_i)\rangle$ up to phase. For every $\alpha$ and $\psi$, Fig. 1 leaves $\frac{1}{\sqrt2}Z(\alpha)\psi$ on outcome 0 and $\frac{e^{i\alpha}}{\sqrt2}Z(-\alpha)\psi$ on outcome 1.
--   4. **Reachability.** Every level is reached almost surely, with finite mean ladder cost.
--   5. **The run is the circuit.** For every rule, target $\varphi$, input $\psi$, outcomes $\omega$ and time $t$ such that $r_s\ne0$ for all $s<t$, the state of the run is $2^{-t/2}e^{i\gamma}Z(\varphi-r_t)\psi$ for some real $\gamma$.
--   6. **Closest rules exist.**
--   7. **Arbitrary unitary.** Every $U\in U(2)$ has angles $\alpha,\beta,\gamma,\kappa$ with $U=e^{i\kappa}X(\alpha)Z(\beta)X(\gamma)$ such that, for every $\varepsilon>0$ and every closest rule, the three runs with targets $\alpha,\beta,\gamma$ and accuracy $\varepsilon/3$, on independent fair outcomes, almost surely all stop, and the product of the rotations they have applied has accuracy at most $\varepsilon$ against $U$. Their total expected online cost and their total expected offline cost are finite.
--
--   The angles do not depend on $\varepsilon$ or on the rule. The fitted exponents of the paper's abstract are not part of this statement.
--
--   Differences from the source:
--   - encoding: |Z(θ)⟩ written without 1/√2 and post-measurement states written up to normalization → normalized ketZ, unnormalized post-measurement vectors with explicit amplitudes; reason: fixes the constants; the squared norms are the paper's probabilities
--   - reading: Table I says 2θ_i is implementable using |H_i⟩ and the only Clifford named is HSHX, at i = 0 → X H S gives |Z(2θ_i)⟩ for every i; H S H X gives |Z(π/2 − 2θ_i)⟩; reason: H S H X|H_i⟩ differs from |Z(2θ_i)⟩ for i ≥ 1 (overlap 0.902 at i = 1), and the two agree at i = 0
--   - reading: 0 < θ_i < π/4 (∀i) → every level i ≥ 0 (clause 2); reason: at i = −1, θ = π/4 and p = 1/2, so the paper's ∀i can only range over the levels of the ladder
--   - reading: each step costs one copy, except the first node, which costs two, and two new copies after outcome 1 there (p. 3, Fig. 3) → a walk from a level −1, no state held, with one copy per transition; reason: gives exactly the paper's counts at every node
--   - reading: the walk of Fig. 3 is described with its cost per step, and no termination claim is written → almost sure arrival at every level at finite expected cost (clause 4); reason: the protocol's use of |H_i⟩ on p. 4 assumes each ladder ends with the state
--   - reading: step 3 says 2θ_i is close to φ; p. 3 says closest → a closest level, for every tie-break; reason: p. 3 fixes the meaning; covering every tie-break leaves no case out
--   - reading: the p. 4 step list treats all levels alike; p. 3 says a failed T gate is always corrected deterministically by S → level 0 moves the residual by sign(r)·π/4 whatever the outcome, with S or S† applied when needed; reason: the paper calls this a crucial fact (p. 3); without it a failure at level 0 would not be corrected
--   - reading: we can actually apply any Z-rotation rapidly and with good accuracy (p. 3), supported by simulation → almost sure stopping at accuracy ε, with finite expected online and offline cost, for every ε > 0; reason: the source gives no quantified statement of rapidly; its only quantified form is a fit on 10⁻¹² < ϵ < 10⁻⁴, which is not a claim about all ϵ
--   - reading: three rotations produce any unitary, with no split of the accuracy → each rotation is run to accuracy ε/3; reason: the source does not say how the accuracy is shared; the overall accuracy is still ε
--   - generalization: the simulation takes 0 < φ < 2π → every real target φ; reason: specializes to the simulated range
--   - generalization: the protocol uses the closest level → the amplitude identity of clause 5 holds for every rule; reason: specializes to closest rules
--   - encoding: one simulated ladder per step, averaged → each step's ladder enters through its mean cost; reason: the ladder randomness is independent of the outcomes, so the expectations agree
--   - encoding: an analogous circuit performs a rotation about the X-axis → X(α) := H Z(α) H; reason: conjugation by the Clifford H exchanges the two axes
--   - encoding: U ∝ X(α)Z(β)X(γ) → U = e^{iκ} X(α)Z(β)X(γ); reason: a proportionality constant between unitaries is a phase
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, title claim, unnumbered, with Sec. II, pp. 2-3, Sec. III, pp. 3-4 and p. 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_RotationLadder_Protocol_IsClosestRule
import Definitions.Def_RotationLadder_Protocol_angle
import Definitions.Def_RotationLadder_Protocol_applied
import Definitions.Def_RotationLadder_Protocol_cnotSecond
import Definitions.Def_RotationLadder_Protocol_coinLaw
import Definitions.Def_RotationLadder_Protocol_ketH
import Definitions.Def_RotationLadder_Protocol_ketZ
import Definitions.Def_RotationLadder_Protocol_ladderMeanCost
import Definitions.Def_RotationLadder_Protocol_offlineCost
import Definitions.Def_RotationLadder_Protocol_postOut
import Definitions.Def_RotationLadder_Protocol_runKet
import Definitions.Def_RotationLadder_Protocol_xRot
open scoped ENNReal

namespace RotationLadder.Protocol

/-- **The protocol implements every single-qubit unitary.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, unnumbered: the title claim, with Sec. II (pp. 2-3), Sec. III (pp. 3-4) and p. 5.

1. Fig. 2 moves `|H_i⟩` up on outcome `0` and down on outcome `1`, with amplitudes `√p_(0,i)`,
   `√(1 - p_(0,i))`.
2. `3/4 ≤ p_(0,i) < cos²(π/8)` and `0 < θ_i < π/4`.
3. A Clifford turns `|H_i⟩` into `|Z(2θ_i)⟩`, and Fig. 1 applies `Z(±α)` with amplitude `1/√2`.
4. Every level is reached almost surely at finite mean cost.
5. For every input state and every outcome sequence, a run that has not reached residual `0` holds
   the state `Z(φ - r_t)ψ` up to phase, with amplitude `2^(-t/2)`.
6. A closest rule exists.
7. Every `U ∈ U(2)` is `e^(iκ) X(α)Z(β)X(γ)`, and for every `ε > 0` and every closest rule the three
   runs with accuracy `ε/3` almost surely stop and give accuracy at most `ε`, at finite expected
   online and offline cost.

**Formalization Note.** The angles `α, β, γ, κ` come before `ε`, so they depend on `U` only. The
paper's fitted exponents are not part of this statement. Clause 5 holds for every rule, not only
closest ones. -/
theorem arbitrary_rotation_protocol :
    (∀ i : ℕ,
      postOut false (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketH 0) (ketH i))) =
          ((Real.sqrt (ladderProb i) : ℝ) : ℂ) • ketH ((i : ℤ) + 1) ∧
      postOut true (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketH 0) (ketH i))) =
          ((Real.sqrt (1 - ladderProb i) : ℝ) : ℂ) • ketH ((i : ℤ) - 1)) ∧
    (∀ i : ℕ, 3 / 4 ≤ ladderProb i ∧ ladderProb i < Real.cos (Real.pi / 8) ^ 2 ∧
      0 < theta i ∧ theta i < Real.pi / 4) ∧
    ((∀ i : ℕ, ∃ γ : ℝ,
      QAlgorithms.act (QAlgorithms.pauliX * QAlgorithms.hadamard * QAlgorithms.phaseS) (ketH i) =
        Complex.exp (Complex.I * (γ : ℂ)) • ketZ (angle i)) ∧
    (∀ (α : ℝ) (ψ : EuclideanSpace ℂ Bool),
      postOut false (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketZ α) ψ)) =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • QAlgorithms.act (zRot α) ψ ∧
      postOut true (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketZ α) ψ)) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.exp (Complex.I * (α : ℂ))) • QAlgorithms.act (zRot (-α)) ψ)) ∧
    (∀ i : ℕ, (∀ᵐ u ∂ladderLaw, ladderCost i u < ⊤) ∧ ladderMeanCost i < ⊤) ∧
    (∀ (pick : ℝ → ℕ) (φ : ℝ) (ψ : EuclideanSpace ℂ Bool) (ω : Coins) (t : ℕ),
      (∀ s < t, residual pick φ ω s ≠ 0) →
      ∃ γ : ℝ, runKet pick φ ψ ω t =
        ((((Real.sqrt 2)⁻¹ ^ t : ℝ) : ℂ) * Complex.exp (Complex.I * (γ : ℂ))) •
          QAlgorithms.act (zRot (φ - residual pick φ ω t)) ψ) ∧
    (∃ pick : ℝ → ℕ, IsClosestRule pick) ∧
    (∀ U ∈ Matrix.unitaryGroup Bool ℂ, ∃ α β γ κ : ℝ,
      U = Complex.exp (Complex.I * (κ : ℂ)) • (xRot α * zRot β * xRot γ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ pick : ℝ → ℕ, IsClosestRule pick →
        (∀ᵐ ω ∂(coinLaw.prod (coinLaw.prod coinLaw)),
          stopTime pick α (ε / 3) ω.1 < ⊤ ∧ stopTime pick β (ε / 3) ω.2.1 < ⊤ ∧
          stopTime pick γ (ε / 3) ω.2.2 < ⊤ ∧
          accuracy U (xRot (applied pick α (ε / 3) ω.1) * zRot (applied pick β (ε / 3) ω.2.1) *
            xRot (applied pick γ (ε / 3) ω.2.2)) ≤ ε) ∧
        (∫⁻ ω, ((stopTime pick α (ε / 3) ω.1 + stopTime pick β (ε / 3) ω.2.1 +
            stopTime pick γ (ε / 3) ω.2.2 : ℕ∞) : ℝ≥0∞)
          ∂(coinLaw.prod (coinLaw.prod coinLaw)) < ⊤) ∧
        (∫⁻ ω, (offlineCost pick α (ε / 3) ω.1 + offlineCost pick β (ε / 3) ω.2.1 +
            offlineCost pick γ (ε / 3) ω.2.2)
          ∂(coinLaw.prod (coinLaw.prod coinLaw)) < ⊤)) := by sorry

end RotationLadder.Protocol
