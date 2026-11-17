-- Prove2me | Theorems.Thm_PopRAM_Supplement_theorem_4
-- name    : PopRAM.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:33:03.261103+00:00
-- url     : https://prove2.me/theorems/627b6c33-f6fd-44bf-8833-f98dab3c654e
-- title:
--   Theorem 4 — the MC+ simulation in the same time with $O((\rho'+w)\,w\,(T_Rw+T_{RAM}+T_P))$ states
-- statement:
--   Let $\mathcal P$ be a $\mathcal P$-program and $S=T_Rw+T_{RAM}+T_P$, so that the MC+ simulation of Theorem 3 runs in $\tau=O(wS)$ rounds. For every integer $C\ge 2$ and every $\eta>0$ there are $K,w_0$ with: for every $w\ge w_0$ there are a population protocol with at most
--   $$K\,(\rho'+w)\,w\,S$$
--   states and a set $\mathrm{Anom}$ of **anomaly states** such that on $n=n_w$ agents, for every admissible input $k$ and every unary placement of it,
--
--   1. with probability at least $1-n^{-\eta}$ there is a time
--   $$t\le K\,n\,(\rho'w+w^2S)$$
--   (the time bound of Theorem 3) at which the configuration is silent with the program's output counts, and no agent is in an anomaly state at any time up to $t$;
--   2. from every configuration reachable from the initial one, the expected number of interactions until a silent configuration with the program's output counts, or a configuration containing an anomaly state, is at most $n^K$.
--
--   Compared with Theorem 3, the time and the anomaly-detection guarantees are unchanged and the number of states drops from $O(\rho'w\tau)$ to $O((\rho'+w)\tau)$, a saving of a factor $\Theta(\min(\rho',w))$. The refined protocol is a different protocol from that of Theorem 3: every instruction emulation and conversion is padded to a fixed-length pass, so that bit indices are a function of the round.
--
--   **Formalization Note** The MC+ notion is that of [GGJ+26] and is not defined in the paper; it is read exactly as in the published Theorem 3 (`PopRAM.theorem_3`), through the three properties the paper lists on p.10 as those Theorem 2(ii) uses. The protocol is quantified separately from Theorem 3's.
--
--   Differences from the source:
--   - reading: 'the MC+ simulation of Theorem 3' (MC+ is a notion of [GGJ+26]) → whp silent-correct within the time bound with no anomaly state before; polynomial expected time to correct-or-anomaly from every reachable configuration; reason: the reading of the published PopRAM.theorem_3, i.e. the properties listed on p.10 as those Theorem 2(ii) needs
--   - encoding: 'the same number of rounds' (τ rounds of Θ(w) time plus one O(ρ′w) round) → total of K·n·(ρ′w + w²S) interactions, the bound of PopRAM.theorem_3; reason: rounds are internal to the construction; the total time is the statement's content
--   - encoding: O((ρ′ + w)τ) states with τ = O(w(T_R w + T_RAM + T_P)) → card Q ≤ K·(ρ′ + w)·w·S; reason: τ's bound substituted, as Theorem 3 writes O(ρ′wτ) = O(ρ′w²(T_R w + T_RAM + T_P))
--   - encoding: parallel time → interactions (n interactions = one unit of time); reason: the paper defines time as interactions divided by n
--   - reading: 'whp' and population size n_w → every integer C ≥ 2 before η; ∀ η > 0, ∃ K w₀; n = n_w exactly; reason: as in Theorems 1 and 3
--   - encoding: unary input sets X_i and output sets Y_i → input states ι(i), start state q₀ for every other agent, output map Q → Option (Fin T_P); every labelling with counts k; reason: the published SimProtocol interface, as in Theorem 3
--   - reading: Definition 1 'also appl[ies] to the partial input counts used during backup retries' → Definition 1 holds on every tuple k' ≤ k of every admissible k; reason: the published PProgram definition, as in Theorem 3
--   - generalization: Definition 1 for the program at every word length → Definition 1 required only for w ≥ w₁, some w₁; reason: the theorem is claimed for sufficiently large w; a program satisfying Definition 1 at every w has w₁ = 0
--   - reading: ρ′ = ρ + T_R + T_P + O(1) → ρ′ = ρ + T_R + T_P + 4; reason: the published PProgram definition; the paper does not pin its O(1)
--   - encoding: w-RAM of Table 1 with two's-complement words → BitVec w registers, faults for out-of-range or unwritten accesses, JGE on toInt, jump past the end halts; reason: the published WordRAM definition
--   - generalization: 'The simulated P-program has fixed length' (p.7) → an instruction list code w for each w, with lengths bounded uniformly in w; reason: the published PProgram definition; one program independent of w is the constant family
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Theorem 4, p.11 (PDF p.12), restated and proved p.28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_PopRAM_SimProtocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM.Supplement

/-- **Theorem 4** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version sha256
f13223b3…, p.11, PDF p.12; restated and proved p.28, PDF pp.29–30). "The MC+ simulation of
Theorem 3 can be implemented in the same number of rounds and with O((ρ′ + w) τ) states."

For every integer `C ≥ 2` and every `η > 0` there are `K, w₀` with: for every `w ≥ w₀` there are a
protocol with at most `K·(ρ′ + w)·w·S` states and a set `Anom` of anomaly states such that on
`n = n_w` agents, for every admissible input and labelling,
1. with probability at least `1 − n^{-η}`, within `K·n·(ρ′w + w²S)` interactions (the time bound of
   Theorem 3) the run reaches a silent configuration with the program's output counts, and no agent
   is in an anomaly state at any time up to then;
2. from every configuration reachable from the initial one, the expected number of interactions
   until a silent correct configuration or a configuration containing an anomaly state is at most
   `n^K`.

**Formalization Note** The MC+ simulation is read exactly as in `PopRAM.theorem_3` (clauses 1 and 2
there); "the same number of rounds" is that theorem's total time `τ` rounds of `Θ(w)` time plus one
`O(ρ′w)`-time initialisation round, i.e. `O(ρ′w + w²S)` time. `τ = O(w·S)` with
`S = T_R w + T_RAM + T_P`, so `O((ρ′ + w)τ)` states is `K·(ρ′ + w)·w·S`. This is a separate
existence statement: the protocol is the fixed-schedule refinement of App. B, not the one of
Theorem 3. -/
theorem theorem_4 (P : PProgram) :
    ∀ C : ℕ, 2 ≤ C → ∀ η : ℝ, 0 < η → ∃ K w₀ : ℕ, ∀ w ≥ w₀,
      ∃ Sim : SimProtocol (P.TR w) (P.TP w), ∃ Anom : Set Sim.Q,
        Fintype.card Sim.Q ≤ K * (P.rho' w + w) * w * P.S w ∧
        ∀ k ∈ P.adm w, ∀ lab : Fin (P.nPop C w) → Option (Fin (P.TR w)), HasCounts lab k →
          sched (P.nPop C w)
              {ω | ¬ ∃ t : ℕ, t ≤ K * P.nPop C w * (P.rho' w * w + w ^ 2 * P.S w) ∧
                run Sim.δ (Sim.init lab) ω t ∈ Sim.Correct (P.out w k) ∧
                ∀ s ≤ t, ∀ a, run Sim.δ (Sim.init lab) ω s a ∉ Anom}
            ≤ whpBound (P.nPop C w) η ∧
          ∀ c : Fin (P.nPop C w) → Sim.Q, Reachable Sim.δ (Sim.init lab) c →
            ∫⁻ ω, (hit Sim.δ c (Sim.Correct (P.out w k) ∪ {c' | ∃ a, c' a ∈ Anom}) ω : ℝ≥0∞)
                ∂(sched (P.nPop C w))
              ≤ (P.nPop C w : ℝ≥0∞) ^ K := by sorry

end PopRAM.Supplement
