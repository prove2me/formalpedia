-- Prove2me | Theorems.Thm_PopRAM_theorem_3
-- name    : PopRAM.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:59.406201+00:00
-- url     : https://prove2.me/theorems/28a19161-9e50-4af6-963c-7939ec8a091b
-- title:
--   Theorem 3 — the MC+ simulation: whp correct in $O(\rho'w+w^2(T_Rw+T_{RAM}+T_P))$ time, anomalies detected in polynomial expected time
-- statement:
--   Let $\mathcal P$ be a $\mathcal P$-program, $S=T_Rw+T_{RAM}+T_P$. For every integer $C\ge 2$ and every $\eta>0$ there are $K,w_0$ with: for every $w\ge w_0$ there are a population protocol with at most $K\rho'w^2S$ states and a set $\mathrm{Anom}$ of **anomaly states** such that on $n=n_w$ agents, for every admissible input $k$ and every unary placement of it,
--
--   1. with probability at least $1-n^{-\eta}$ there is a time
--   $$t\le K\,n\,(\rho'w+w^2S)$$
--   at which the configuration is silent with the program's output counts, and no agent is in an anomaly state at any time up to $t$;
--   2. from every configuration reachable from the initial one, the expected number of interactions until a silent configuration with the program's output counts, or a configuration containing an anomaly state, is at most $n^K$.
--
--   The paper's statement counts $\tau=O(w(T_Rw+T_{RAM}+T_P))$ rounds of $\Theta(w)$ time each plus one register-initialisation round of $O(\rho'w)$ time, and $O(\rho'w\tau)$ states; the total time is the bound in 1. Clause 2 is the anomaly detection that makes the protocol MC+: every malfunction is eventually signalled, in polynomial expected time from every reachable configuration.
--
--   **Formalization Note** The MC+ notion is that of [GGJ+26] and is not defined in the paper; it is read through the three properties the paper lists on p.10 as those Theorem 2(ii) uses.
--
--   Differences from the source:
--   - reading: an 'efficient MC+ population protocol' (notion of [GGJ+26]) → whp silent-correct within the time bound with no anomaly state before; polynomial expected time to correct-or-anomaly from every reachable configuration; reason: the properties listed on p.10 as those Theorem 2(ii) needs
--   - encoding: τ rounds of Θ(w) time plus one O(ρ′w) round → total of K·n·(ρ′w + w²S) interactions; reason: rounds are internal to the construction; the total time is the statement's content
--   - encoding: parallel time → interactions (n interactions = one unit of time); reason: the paper defines time as interactions divided by n
--   - reading: 'whp' and population size n_w → every integer C ≥ 2 before η; ∀ η > 0, ∃ K w₀; n = n_w exactly; reason: as in Theorem 1
--   - encoding: unary input sets X_i and output sets Y_i, with a distinct input state for each input variable (p.6) → input states ι(i), start state q₀ for every other agent, output map Q → Option (Fin T_P); every labelling with counts k; ι need not be injective; reason: Lean representation of the unary interface; all labellings are equivalent by symmetry; an injective ι follows by adding T_R labelled copies of the input states, which K absorbs
--   - reading: Definition 1 'also appl[ies] to the partial input counts used during backup retries' → Definition 1 holds on every tuple k' ≤ k (coordinatewise) of every admissible k; reason: a backup retry runs the program on a partial count of each input
--   - generalization: Definition 1 for the program at every word length → Definition 1 required only for w ≥ w₁, some w₁; reason: the theorem is claimed for sufficiently large w; a program satisfying Definition 1 at every w has w₁ = 0
--   - reading: ρ′ = ρ + T_R + T_P + O(1) → ρ′ = ρ + T_R + T_P + 4; reason: four auxiliary registers (rp_in, rp_out, r_c, one spare); the paper does not pin its O(1); (T_R + T_P + 1)2^w dominates ρ′w for large w, so the free-agent bound holds with any fixed constant
--   - encoding: w-RAM of Table 1 with two's-complement words → BitVec w registers, faults for out-of-range or unwritten accesses, JGE on toInt, jump past the end halts; reason: Lean representation of the paper's machine and of items 3–4 of Definition 1
--   - generalization: 'The simulated P-program has fixed length' (p.7) → an instruction list code w for each w, with lengths bounded uniformly in w; reason: the proofs use only the fixed length (O(1) states for ip, pp.7, 36), and code, constants and direct addresses are encoded in the transition function for the given w; one program independent of w is the constant family
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Theorem 3, p.10 (PDF p.11), restated p.18 (PDF p.19)

import Mathlib
import Definitions.Def_PopRAM_SimProtocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Theorem 3** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version sha256
f13223b3…, p.10, PDF p.11; restated p.18, PDF p.19). "For every P-program, there exists an
efficient MC+ population protocol that, whp, correctly simulates the program in
τ = O(w(T_R w + T_RAM + T_P)) rounds of Θ(w) time each, plus one register initialisation round
lasting O(ρ′w) time. The protocol uses O(ρ′wτ) = O(ρ′w²(T_R w + T_RAM + T_P)) states."

For every integer `C ≥ 2` and every `η > 0` there are `K, w₀` with: for every `w ≥ w₀` there are a
protocol with at most `K·ρ′w²S` states and a set `Anom` of anomaly states such that on `n = n_w`
agents, for every admissible input and labelling,
1. with probability at least `1 − n^{-η}`, within `K·n·(ρ′w + w²S)` interactions the run reaches a
   silent configuration with the program's output counts, and no agent is in an anomaly state at
   any time up to then;
2. from every configuration reachable from the initial one, the expected number of interactions
   until a silent correct configuration or a configuration containing an anomaly state is at most
   `n^K`.

**Formalization Note** "MC+" is the notion of [GGJ+26], not defined in this paper. It is read
through the properties the paper lists on p.10 as those Theorem 2(ii) needs: "every malfunction is
eventually signalled, the expected time to completion or detection is polynomial from every
reachable configuration, and a correct execution becomes silent". The round structure is internal to
the construction; the statement gives its total, `τ` rounds of `Θ(w)` time plus `O(ρ′w)` time, i.e.
`O(ρ′w + w²S)` time. `S = T_R w + T_RAM + T_P`. -/
theorem theorem_3 (P : PProgram) :
    ∀ C : ℕ, 2 ≤ C → ∀ η : ℝ, 0 < η → ∃ K w₀ : ℕ, ∀ w ≥ w₀,
      ∃ Sim : SimProtocol (P.TR w) (P.TP w), ∃ Anom : Set Sim.Q,
        Fintype.card Sim.Q ≤ K * P.rho' w * w ^ 2 * P.S w ∧
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

end PopRAM
