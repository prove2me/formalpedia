-- Prove2me | Theorems.Thm_PopRAM_theorem_1
-- name    : PopRAM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:29.233277+00:00
-- url     : https://prove2.me/theorems/60f225fd-fc71-4992-b8a6-9b3dd6607ef5
-- title:
--   Theorem 1 — every $\mathcal P$-program has a silent stable simulation in $O(w^2(T_Rw+T_{RAM}+T_P))$ time with $O(\rho'w^2(T_Rw+T_{RAM}+T_P))$ states
-- statement:
--   Let $\mathcal P$ be a $\mathcal P$-program with resources $T_R,T_{RAM},T_P,\rho$, write $S=T_Rw+T_{RAM}+T_P$, $\rho'=\rho+T_R+T_P+4$ and $n_w=C((T_R+T_P+1)2^w+\rho'w)$. Then for every integer $C\ge2$ and every $\eta>0$ there are constants $K,w_0$ with the following property. For every $w\ge w_0$ there is a population protocol with at most
--   $$K\,\rho' w^2 S$$
--   states such that on $n=n_w$ agents, for every admissible input tuple $k$ and every placement of $k$ in unary on the agents, the run under the uniform random scheduler, with stabilisation time $\tau$ = first time the configuration is silent and its output counts equal the program's outputs on $k$, satisfies
--
--   1. $\Pr[\tau<\infty]=1$ (the protocol is stable and silent);
--   2. $\mathbb E[\tau]\le K\,n\,w^2S$ interactions, i.e. expected time $O(w^2S)$;
--   3. $\Pr[\tau\le K\,n\,w^2S]\ge 1-n^{-\eta}$.
--
--   This is the paper's main result: efficient, stable and silent population computation of every word-RAM program with polynomial resources in $w=\Theta(\log n)$.
--
--   **Formalization Note** The protocol may depend on $w$ and $\eta$ ("with the protocol constants chosen accordingly", p.1) but not on the input. $C$ is arbitrary: the paper calls it a fixed integer constant $C>1$ (p.6), never chooses it, and its proofs use only $C>1$; $K,w_0$ may depend on $C$. One constant $K$ serves the state bound, the expected bound and the high-probability bound.
--
--   Differences from the source:
--   - encoding: parallel time → interactions (n interactions = one unit of time); reason: the paper defines time as interactions divided by n
--   - encoding: stabilisation time of a silent protocol → hitting time of the set of silent configurations with the program's output counts; reason: silent configurations are absorbing, so this is the moment after which no agent changes state
--   - reading: 'whp': probability at least 1 − n^{−η} 'for any prescribed constant η > 0, with the protocol constants chosen accordingly' → ∀ η > 0, ∃ K w₀, ∀ w ≥ w₀, ∃ protocol; reason: the protocol and its constants may depend on η
--   - reading: population size n_w with 'C > 1 a fixed integer constant' → every C ∈ ℕ with C ≥ 2, before η (K, w₀ may depend on C); n = n_w exactly; reason: the paper never chooses C and its proofs use only C > 1, so the result holds for each fixed C, which implies existence of one; the printed theorem speaks of population size n_w
--   - encoding: unary input sets X_i and output sets Y_i, with a distinct input state for each input variable (p.6) → input states ι(i), start state q₀ for every other agent, output map Q → Option (Fin T_P); every labelling with counts k; ι need not be injective; reason: Lean representation of the unary interface; all labellings are equivalent by symmetry; an injective ι follows by adding T_R labelled copies of the input states, which K absorbs
--   - reading: Definition 1 'also appl[ies] to the partial input counts used during backup retries' → Definition 1 holds on every tuple k' ≤ k (coordinatewise) of every admissible k; reason: a backup retry runs the program on a partial count of each input
--   - generalization: Definition 1 for the program at every word length → Definition 1 required only for w ≥ w₁, some w₁; reason: the theorem is claimed for sufficiently large w; a program satisfying Definition 1 at every w has w₁ = 0
--   - reading: ρ′ = ρ + T_R + T_P + O(1) → ρ′ = ρ + T_R + T_P + 4; reason: four auxiliary registers (rp_in, rp_out, r_c, one spare); the paper does not pin its O(1); (T_R + T_P + 1)2^w dominates ρ′w for large w, so the free-agent bound holds with any fixed constant
--   - encoding: w-RAM of Table 1 with two's-complement words → BitVec w registers, faults for out-of-range or unwritten accesses, JGE on toInt, jump past the end halts; reason: Lean representation of the paper's machine and of items 3–4 of Definition 1
--   - generalization: 'The simulated P-program has fixed length' (p.7) → an instruction list code w for each w, with lengths bounded uniformly in w; reason: the proofs use only the fixed length (O(1) states for ip, pp.7, 36), and code, constants and direct addresses are encoded in the transition function for the given w; one program independent of w is the constant family
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Theorem 1, p.6 (PDF p.7), ll.287–290

import Mathlib
import Definitions.Def_PopRAM_SimProtocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Theorem 1** (Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by
Population Protocols*, arXiv:2611.06178, held version sha256 f13223b3…, p.6, PDF p.7, ll.287–290).
"Every P-program admits an efficient simulation by a silently stabilising probabilistic population
protocol. For all sufficiently large w and population size n_w, the simulation stabilises, both in
expectation and with high probability, in O(w²(T_R w + T_RAM + T_P)) time, using
O(ρ′w²(T_R w + T_RAM + T_P)) states."

For every P-program, every integer `C ≥ 2` and every `η > 0` there are `K, w₀` with:
for every `w ≥ w₀` there is a protocol with at most `K·ρ′w²S` states (`S = T_R w + T_RAM + T_P`)
such that on `n = n_w` agents, for every admissible input `k` and every labelling with counts `k`,
the run started from the labelled configuration
1. reaches a silent configuration with the program's output counts with probability `1`;
2. reaches it within expected `K·n·w²S` interactions (time `K·w²S`);
3. reaches it within `K·n·w²S` interactions with probability at least `1 − n^{-η}`.

**Formalization Note** Time is counted in interactions (`n` interactions = one unit of parallel
time). The stabilisation time is the hitting time of `Correct`, the first silent configuration with
the right output counts. The protocol may depend on `w` and `η` ("with the protocol constants chosen
accordingly", p.1), never on the input. `C` is arbitrary: the paper calls it "a fixed integer constant"
`C > 1` (p.6), never chooses it, and uses only `C > 1`. Probabilities are measures of the failure events. -/
theorem theorem_1 (P : PProgram) :
    ∀ C : ℕ, 2 ≤ C → ∀ η : ℝ, 0 < η → ∃ K w₀ : ℕ, ∀ w ≥ w₀,
      ∃ Sim : SimProtocol (P.TR w) (P.TP w),
        Fintype.card Sim.Q ≤ K * P.rho' w * w ^ 2 * P.S w ∧
        ∀ k ∈ P.adm w, ∀ lab : Fin (P.nPop C w) → Option (Fin (P.TR w)), HasCounts lab k →
          sched (P.nPop C w)
              {ω | hit Sim.δ (Sim.init lab) (Sim.Correct (P.out w k)) ω = ⊤} = 0 ∧
          ∫⁻ ω, (hit Sim.δ (Sim.init lab) (Sim.Correct (P.out w k)) ω : ℝ≥0∞)
              ∂(sched (P.nPop C w)) ≤ ((K * P.nPop C w * w ^ 2 * P.S w : ℕ) : ℝ≥0∞) ∧
          sched (P.nPop C w)
              {ω | ((K * P.nPop C w * w ^ 2 * P.S w : ℕ) : ℕ∞) <
                hit Sim.δ (Sim.init lab) (Sim.Correct (P.out w k)) ω}
            ≤ whpBound (P.nPop C w) η := by sorry

end PopRAM
