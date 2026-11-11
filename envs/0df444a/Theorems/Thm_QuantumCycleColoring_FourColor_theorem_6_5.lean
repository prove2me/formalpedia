-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_theorem_6_5
-- name    : QuantumCycleColoring.FourColor.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:01:05.759412+00:00
-- url     : https://prove2.me/theorems/c3f43772-9295-483d-a033-d92910079d9b
-- title:
--   Theorem 6.5: every 4-outcome POVM has total $\Lambda$-energy $\Omega(1)$, so cycles cannot be 4-coloured
-- statement:
--   1. There is a universal constant $c>0$ such that for every local dimension $N$, every 4-outcome POVM $\{P_i\}_{i\in[4]}$ on $\mathbb C^N\otimes\mathbb C^N$ and every PSD $N\times N$ matrix $\Lambda$ with $\|\Lambda\|_F=1$,
--   $$\sum_{i\in[4]}\mathcal E_\Lambda(P_i)\ge c .$$
--   2. Consequently, one-way one-round anonymous quantum algorithms cannot solve directed-cycle 4-colouring: for every family of such algorithms, one for each cycle length $n\ge3$ (the registers, the state $\rho_n$ and the POVM $P^{(n)}$ may all depend on $n$), the probability that the output is a proper 4-colouring of the directed $n$-cycle does not tend to $1$ as $n\to\infty$.
--
--   Part 1 is the paper's formal main theorem; part 2 is its algorithmic consequence, the impossibility of solving the problem with high probability.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - reading: ∑_{i∈[4]} E_Λ(P_i) = Ω(1) → one explicit constant ∃ K > 0 quantified before every other object (dimension, operators, Λ); reason: the paper's O(·)/Ω(1) constants are absolute; this is the strongest reading
--   - generalization: "cannot solve" = no algorithm succeeds with high probability, i.e. with probability at least 1 − 1/poly(n) on every n-cycle (Definition 3.8, p.19) → for every family of algorithms indexed by n, the proper-colouring probability on the (m+3)-cycle does not tend to 1 as m → ∞; reason: success with probability ≥ 1 − 1/poly(n) implies convergence to 1, so the Lean statement implies the paper's under every reading of 1/poly(n)
--   - generalization: an algorithm in the normal form of §6.1 (every node prepares a pure state |Ψ⟩ on ℂ^N ⊗ ℂ^N and measures a POVM on ℂ^N ⊗ ℂ^N), to which Definition 3.10's arbitrary finite algorithm is reduced → every node prepares an arbitrary density matrix ρ on A × B (arbitrary finite index types a, b) and measures an arbitrary POVM on B × A (received B, own A); the output law is the Born rule of the whole n-node experiment; reason: contains the normal form (a = b = Fin N, ρ = |vec Λ̄⟩⟨vec Λ̄|) and every finite-dimensional one-way one-round algorithm of Definition 3.10, with private randomness and workspace absorbed into A and the mixed state ρ
--   - encoding: directed n-cycle with nodes v_i, i ∈ ℤ_n, n ≥ 3 → nodes ZMod n with an instance NeZero n (needed to sum over the finite set of node labels) and the hypothesis 3 ≤ n; reason: NeZero n is implied by 3 ≤ n; the same cycles
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Theorem 6.5, p.43 (proof pp.44–47)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix Filter Topology

/-- Theorem 6.5, p.43 (Gur–Li, STOC 2027 #515).
(i) There is a universal `c > 0` such that for every 4-outcome POVM `{P_i}` on `ℂ^d ⊗ ℂ^d` and
every PSD `Λ` with `‖Λ‖_F = 1`, `∑_{i∈[4]} E_Λ(P_i) ≥ c`.
(ii) Consequently one-way one-round anonymous quantum algorithms cannot solve directed-cycle
4-colouring: for every family of such algorithms, one for each cycle length `n ≥ 3` (local
dimensions `a n`, `b n`, state `ρ n`, POVM `P n` all allowed to depend on `n`), the probability that
the `n`-cycle is properly 4-coloured does not tend to `1` as `n → ∞`. -/
theorem theorem_6_5 :
    (∃ c : ℝ, 0 < c ∧
      ∀ (d : Type) [Fintype d] [DecidableEq d] (P : Fin 4 → Matrix (d × d) (d × d) ℂ),
        FuchsVdGraaf.IsPOVM P →
        ∀ (Λ : Matrix d d ℂ), Λ.PosSemidef → frobNorm Λ = 1 →
        c ≤ ∑ i, energy Λ (P i)) ∧
    (∀ (a b : ℕ → Type) [∀ n, Fintype (a n)] [∀ n, DecidableEq (a n)] [∀ n, Fintype (b n)]
        [∀ n, DecidableEq (b n)] (ρ : ∀ n, Matrix (a n × b n) (a n × b n) ℂ)
        (P : ∀ n, Fin 4 → Matrix (b n × a n) (b n × a n) ℂ),
        (∀ n, IsDensityMatrix (ρ n)) → (∀ n, FuchsVdGraaf.IsPOVM (P n)) →
        ¬ Tendsto (fun m : ℕ => properColoringProb (m + 3) (ρ (m + 3)) (P (m + 3)))
          atTop (𝓝 1)) := by sorry

end QuantumCycleColoring.FourColor
