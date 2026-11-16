-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_Supplement_theorem_C_1
-- name    : QuantumSymmetryBreaking.CycleColoring.Supplement.theorem_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:10:32.196818+00:00
-- url     : https://prove2.me/theorems/92d12eaf-558b-4d8b-aff2-3abb2b76a5c3
-- title:
--   Theorem C.1 — Exact qubit lower bound for anonymous cycle coloring
-- statement:
--   Fix an integer q≥2. For any anonymous one-way one-round algorithm on a directed n-cycle with n≥3, let k≥0 be the number of qubits sent per node. The private register has any positive finite dimension, the prepared state can be mixed, and the final measurement is any q-outcome POVM. If ε>0 and each edge is monochromatic with probability at most ε under the full Born law, then
--
--   $$\varepsilon\ge\frac{1}{q^3 2^{11k}},\qquad k\ge\frac{\log_2(1/(q^3\varepsilon))}{11}.$$
--
--   These are the exact inequalities in the final proof display on printed p.49, retaining the q-dependent term and the base-two logarithm. For fixed q they imply the stated asymptotic lower bound; no uniform error threshold independent of q is asserted. This is the communication lower-bound companion theorem.
--
--   Differences from the source:
--   - encoding: Ω(log(1/ε)) for fixed q → both exact necessary inequalities from the final proof display on p.49; reason: the constants are supplied by the source itself; log₂ x is Real.log x / Real.log 2
--   - encoding: arbitrary finite private space and k transmitted qubits → Fin D × Fin (2 ^ k), D > 0, general mixed state and POVM; reason: no private-space cap or normal-form assumption is introduced
--   - encoding: directed n-cycle and per-edge failure bound → n ≥ 3, NeZero n and every i in ZMod n; q colors are Fin q; reason: explicit source graph and palette indexing, using the full collisionProb law
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), Theorem C.1, p.46 (PDF 49); exact bound p.49 (PDF 52)

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization

set_option autoImplicit false
open scoped ComplexOrder

namespace QuantumSymmetryBreaking.CycleColoring.Supplement

open QuantumCycleColoring.FourColor

/-- Theorem C.1, printed p.46 (PDF 49), exact necessary inequalities from
its final proof display, printed p.49 (PDF 52). The logarithm is base two.
No restriction on the private register or the input mixed state. -/
theorem theorem_C_1 (q k D n : ℕ) [NeZero n] (hq : 2 ≤ q) (hD : 0 < D) (hn : 3 ≤ n)
    (ε : ℝ) (hε : 0 < ε)
    (ρ : Matrix (Fin D × Fin (2 ^ k)) (Fin D × Fin (2 ^ k)) ℂ)
    (hρ : IsDensityMatrix ρ)
    (Q : Fin q → Matrix (Fin (2 ^ k) × Fin D) (Fin (2 ^ k) × Fin D) ℂ)
    (hQ : IsPOVM Q) (hError : ∀ i : ZMod n, collisionProb n ρ Q i ≤ ε) :
    1 / ((q : ℝ) ^ 3 * (2 : ℝ) ^ (11 * k)) ≤ ε ∧
    Real.log (1 / ((q : ℝ) ^ 3 * ε)) / Real.log 2 / 11 ≤ (k : ℝ) := by sorry

end QuantumSymmetryBreaking.CycleColoring.Supplement
