-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_theorem_1_1
-- name    : QuantumCycleColoring.FourColor.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:01:28.851197+00:00
-- url     : https://prove2.me/theorems/580125b3-474d-4561-9ffa-94d3e579c857
-- title:
--   Theorem 1.1: every one-way one-round quantum 4-colouring of a directed cycle has constant collision probability
-- statement:
--   There is a universal constant $C>0$ such that for every directed $n$-cycle ($n\ge3$) and every one-way one-round anonymous quantum algorithm that assigns each node $v_i$ a colour $c_i\in[4]$,
--   $$\Pr[c_i=c_{i+1}]\ge C\qquad\text{for every } i\in\mathbb Z_n .$$
--   Here every node prepares the same state $\rho$ on a kept register $A$ and a message register $B$ (arbitrary finite dimensions), sends $B$ to its successor, and measures the same 4-outcome POVM on the received register and its own $A$; the probability is that of the Born rule for the whole $n$-node experiment. The constant does not depend on $n$, on the local dimensions, on the state or on the POVM.
--
--   This is the paper's headline result: no one-way one-round quantum algorithm can 4-colour a directed cycle, since every edge fails with a constant probability.
--
--   Differences from the source:
--   - generalization: an algorithm in the normal form of §6.1 (every node prepares a pure state |Ψ⟩ on ℂ^N ⊗ ℂ^N and measures a POVM on ℂ^N ⊗ ℂ^N), to which Definition 3.10's arbitrary finite algorithm is reduced → every node prepares an arbitrary density matrix ρ on A × B (arbitrary finite index types a, b) and measures an arbitrary POVM on B × A (received B, own A); the output law is the Born rule of the whole n-node experiment; reason: contains the normal form (a = b = Fin N, ρ = |vec Λ̄⟩⟨vec Λ̄|) and every finite-dimensional one-way one-round algorithm of Definition 3.10, with private randomness and workspace absorbed into A and the mixed state ρ
--   - encoding: directed n-cycle with nodes v_i, i ∈ ℤ_n, n ≥ 3 → nodes ZMod n with an instance NeZero n (needed to sum over the finite set of node labels) and the hypothesis 3 ≤ n; reason: NeZero n is implied by 3 ≤ n; the same cycles
--   - encoding: colours c_i ∈ [4] → colours Fin 4; reason: 0-based labels; the same colourings
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Theorem 1.1, p.4 (formal counterpart Theorem 6.5, p.43, via §6.1, pp.40–41)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix Filter Topology

/-- Theorem 1.1, p.4 (Gur–Li, STOC 2027 #515). There is a universal constant `C > 0` such
that for every directed `n`-cycle (`n ≥ 3`) and every one-way one-round anonymous quantum
algorithm assigning each node a colour in `[4]` (every node prepares the same state `ρ` on a kept
register `A` and a message register `B`, sends `B` to its successor, and measures the same
4-outcome POVM `P` on the received `B` and its own `A`), `Pr[c_i = c_{i+1}] ≥ C` for every edge
`i ∈ ℤ_n`. -/
theorem theorem_1_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) [NeZero n], 3 ≤ n →
    ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (ρ : Matrix (a × b) (a × b) ℂ), IsDensityMatrix ρ →
      ∀ (P : Fin 4 → Matrix (b × a) (b × a) ℂ), FuchsVdGraaf.IsPOVM P →
      ∀ i : ZMod n, C ≤ collisionProb n ρ P i := by sorry

end QuantumCycleColoring.FourColor
