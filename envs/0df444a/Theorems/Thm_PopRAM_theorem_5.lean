-- Prove2me | Theorems.Thm_PopRAM_theorem_5
-- name    : PopRAM.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:27:39.512956+00:00
-- url     : https://prove2.me/theorems/1d10e36d-f04c-460d-aca9-05300107c570
-- title:
--   Theorem 5 — the backup simulation silently stabilises in expected $O(n^2w)$ time with $O(\rho'w^2)$ states
-- statement:
--   Let $\mathcal P$ be a $\mathcal P$-program. For every integer $C\ge2$ there are constants $K,w_0$ such that for every $w\ge w_0$ there is a population protocol with at most $K\rho'w^2$ states such that on $n=n_w$ agents, for every admissible input $k$ and every unary placement of it, the stabilisation time $\tau$ (first silent configuration with the program's output counts) satisfies
--
--   1. $\Pr[\tau<\infty]=1$;
--   2. $\mathbb E[\tau]\le K\,n\cdot n^2w$ interactions, i.e. expected time $O(n^2w)$.
--
--   The backup is the stable component combined with the MC+ simulation in the proof of Theorem 1. Its state bound has no factor $T$, so it does not follow from Theorem 1.
--
--   **Formalization Note** The backup is stated from the standard initial configuration (inputs in their input states, every other agent in one start state); in the paper it is entered through the MC+ handover.
--
--   Differences from the source:
--   - reading: the backup entered from the MC+ handover → the protocol run standalone from the standard unary initial configuration; reason: Theorem 5 is stated for the backup protocol itself; on first entry every non-input agent is a rank-1 leader (p.30)
--   - encoding: O(ρ′w log n) = O(ρ′w²) states → K·ρ′·w² states; reason: at n = n_w, log n = Θ(w) (Fact 2); the printed equality
--   - encoding: parallel time → interactions (n interactions = one unit of time); reason: the paper defines time as interactions divided by n
--   - reading: population size n_w with C > 1 a fixed integer → every integer C ≥ 2; n = n_w exactly; reason: as in Theorem 1
--   - encoding: unary input sets X_i and output sets Y_i, with a distinct input state for each input variable (p.6) → input states ι(i), start state q₀ for every other agent, output map Q → Option (Fin T_P); every labelling with counts k; ι need not be injective; reason: Lean representation of the unary interface; all labellings are equivalent by symmetry; an injective ι follows by adding T_R labelled copies of the input states, which K absorbs
--   - reading: Definition 1 'also appl[ies] to the partial input counts used during backup retries' → Definition 1 holds on every tuple k' ≤ k (coordinatewise) of every admissible k; reason: a backup retry runs the program on a partial count of each input
--   - generalization: Definition 1 for the program at every word length → Definition 1 required only for w ≥ w₁, some w₁; reason: the theorem is claimed for sufficiently large w; a program satisfying Definition 1 at every w has w₁ = 0
--   - reading: ρ′ = ρ + T_R + T_P + O(1) → ρ′ = ρ + T_R + T_P + 4; reason: four auxiliary registers (rp_in, rp_out, r_c, one spare); the paper does not pin its O(1); (T_R + T_P + 1)2^w dominates ρ′w for large w, so the free-agent bound holds with any fixed constant
--   - encoding: w-RAM of Table 1 with two's-complement words → BitVec w registers, faults for out-of-range or unwritten accesses, JGE on toInt, jump past the end halts; reason: Lean representation of the paper's machine and of items 3–4 of Definition 1
--   - generalization: 'The simulated P-program has fixed length' (p.7) → an instruction list code w for each w, with lengths bounded uniformly in w; reason: the proofs use only the fixed length (O(1) states for ip, pp.7, 36), and code, constants and direct addresses are encoded in the transition function for the given w; one program independent of w is the constant family
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Theorem 5, p.11 (PDF p.12), restated p.35 (PDF p.36)

import Mathlib
import Definitions.Def_PopRAM_SimProtocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Theorem 5** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version sha256
f13223b3…, p.11, PDF p.12; restated p.35, PDF p.36). "For every P-program, the backup simulation
population protocol silently stabilises in expected time O(n²w), and uses O(ρ′w log n) = O(ρ′w²)
states."

For every integer `C ≥ 2` there are `K, w₀` such that for every `w ≥ w₀` there is a protocol with at most `K·ρ′w²`
states such that on `n = n_w` agents, for every admissible input and labelling, the run reaches a
silent configuration with the program's output counts with probability `1`, within expected
`K·n·n²w` interactions (time `K·n²w`).

**Formalization Note** The backup is stated standalone, from the standard initial configuration
(input agents in their input states, every other agent in `q₀`); in the paper it is entered from the
MC+ handover. At `n = n_w` one has `log n = Θ(w)` (Fact 2), so the paper's `O(ρ′w log n)` is the
printed `O(ρ′w²)`. No probability parameter `η` occurs: the statement is about expectation only. -/
theorem theorem_5 (P : PProgram) :
    ∀ C : ℕ, 2 ≤ C → ∃ K w₀ : ℕ, ∀ w ≥ w₀,
      ∃ Sim : SimProtocol (P.TR w) (P.TP w),
        Fintype.card Sim.Q ≤ K * P.rho' w * w ^ 2 ∧
        ∀ k ∈ P.adm w, ∀ lab : Fin (P.nPop C w) → Option (Fin (P.TR w)), HasCounts lab k →
          sched (P.nPop C w)
              {ω | hit Sim.δ (Sim.init lab) (Sim.Correct (P.out w k)) ω = ⊤} = 0 ∧
          ∫⁻ ω, (hit Sim.δ (Sim.init lab) (Sim.Correct (P.out w k)) ω : ℝ≥0∞)
              ∂(sched (P.nPop C w))
            ≤ ((K * P.nPop C w * (P.nPop C w ^ 2 * w) : ℕ) : ℝ≥0∞) := by sorry

end PopRAM
