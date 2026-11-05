-- Prove2me | Theorems.Thm_RotationLadder_Protocol_resource_clifford
-- name    : RotationLadder.Protocol.resource_clifford
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:41.529147+00:00
-- url     : https://prove2.me/theorems/6821e06a-2d94-4e00-86ad-b7d990026f85
-- title:
--   The Clifford that turns $|H_i\rangle$ into $|Z(2\theta_i)\rangle$
-- statement:
--   For every level $i\ge0$, up to a global phase,
--
--   $$XHS\,|H_i\rangle=|Z(2\theta_i)\rangle,\qquad\qquad HSHX\,|H_i\rangle=|Z(\pi/2-2\theta_i)\rangle .$$
--
--   At $i=0$ both give $|Z(\pi/4)\rangle$, the $XY$-plane version of $|H\rangle$ displayed in the paper. The first identity is what makes the rotation by $2\theta_i$ of Table I available through the circuit of Fig. 1.
--
--   Differences from the source:
--   - reading: Table I says 2θ_i is implementable using |H_i⟩ and the only Clifford named is HSHX, at i = 0 → X H S gives |Z(2θ_i)⟩ for every i; H S H X gives |Z(π/2 − 2θ_i)⟩; reason: H S H X|H_i⟩ differs from |Z(2θ_i)⟩ for i ≥ 1 (overlap 0.902 at i = 1), and the two agree at i = 0
--   - encoding: |Z(π/4)⟩ = HSHX|H⟩ = |0⟩ + e^{iπ/4}|1⟩ → equality up to a global phase, with normalized ketZ; reason: the paper's display holds up to phase and normalization
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2 and Sec. II, Table I, p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_RotationLadder_Protocol_angle
import Definitions.Def_RotationLadder_Protocol_ketH
import Definitions.Def_RotationLadder_Protocol_ketZ

namespace RotationLadder.Protocol

/-- **The Clifford that makes the rotation resource.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, p. 2 and Table I, p. 3.

Up to a global phase, `X H S |H_i⟩ = |Z(2θ_i)⟩` and `H S H X |H_i⟩ = |Z(π/2 - 2θ_i)⟩` for every level
`i`. At `i = 0` the second is the paper's `|Z(π/4)⟩ = H S H X |H⟩`.

**Formalization Note.** The paper names no Clifford for `i ≥ 1`. Products act right to left, so `S`
acts first in `X H S`, and `X` first in `H S H X`. -/
theorem resource_clifford :
    (∀ i : ℕ, ∃ γ : ℝ,
      QAlgorithms.act (QAlgorithms.pauliX * QAlgorithms.hadamard * QAlgorithms.phaseS) (ketH i) =
        Complex.exp (Complex.I * (γ : ℂ)) • ketZ (angle i)) ∧
    (∀ i : ℕ, ∃ γ : ℝ,
      QAlgorithms.act
          (QAlgorithms.hadamard * QAlgorithms.phaseS * QAlgorithms.hadamard * QAlgorithms.pauliX)
          (ketH i) =
        Complex.exp (Complex.I * (γ : ℂ)) • ketZ (Real.pi / 2 - angle i)) ∧
    (∃ γ : ℝ,
      QAlgorithms.act
          (QAlgorithms.hadamard * QAlgorithms.phaseS * QAlgorithms.hadamard * QAlgorithms.pauliX)
          (ketH 0) =
        Complex.exp (Complex.I * (γ : ℂ)) • ketZ (Real.pi / 4)) := by sorry

end RotationLadder.Protocol
