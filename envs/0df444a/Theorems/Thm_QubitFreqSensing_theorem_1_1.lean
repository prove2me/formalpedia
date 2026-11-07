-- Prove2me | Theorems.Thm_QubitFreqSensing_theorem_1_1
-- name    : QubitFreqSensing.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:07.683523+00:00
-- url     : https://prove2.me/theorems/8e142a82-d63a-4e28-8c22-a74870fe00d6
-- title:
--   Theorem 1.1 — a single-qubit $Y$-pulse protocol detects any of $N$ known frequencies in time $O(\sqrt N/B_{\min}+1/\omega_{\min})$
-- statement:
--   A sensing qubit evolves under either the zero Hamiltonian or $H_{\mathrm{sig}}(t)=B\cos(\omega t+\phi)Z$, where $\omega$ lies in a known finite set $W=\{\omega_1,\dots,\omega_N\}\subset(0,\infty)$, $B\ge B_{\min}$ for a known $B_{\min}>0$, and $B$, $\omega$, $\phi$ are otherwise unknown. Write $\omega_{\min}=\min_i\omega_i$ and $\omega_{\max}=\max_i\omega_i$.
--
--   There is a universal constant $C_0>0$ such that for every finite nonempty $W\subset(0,\infty)$ and every $B_{\min}>0$ there is a single-qubit protocol, depending only on $W$ and $B_{\min}$, built from instantaneous gates and Pauli $Y$ pulses alternating with evolution under the signal, such that:
--
--   1. its total sensing time, including all waits and all repetitions, is at most
--   $$
--   C_0\left(\frac{\sqrt N}{B_{\min}}+\frac1{\omega_{\min}}\right);
--   $$
--   2. each trial uses at most $C_0\,(1+\omega_{\max}N/B_{\min})$ pulses $Y$;
--   3. when the signal is absent it never reports a signal;
--   4. for every $B\ge B_{\min}$, every $\omega\in W$ and every phase $\phi$, it reports a signal with probability at least $2/3$, where absolute time (and so the phase) runs on across trials.
--
--   Its sensing time grows as $\sqrt N$ in the number of candidate frequencies, against $N/B_{\min}$ for a scan of the candidates one by one. Protocol 1 of the paper achieves the theorem with two random pulse patterns from Theorem 5.13, a random wait in $[0,2\pi/\omega_{\min}]$ and $28$ repetitions.
--
--   **Formalization Note** Protocols are the class `Protocol` (see the definition `QubitFreqSensing.PulseProtocol`): a randomized choice among finitely many pulse blocks, each with a wait law supported in $[0,\tau^{\max}]$, a start gate, $Y$ pulses between evolutions and a finish gate, repeated a fixed number of times, with output "present" iff some outcome is $1$.
--
--   Differences from the source:
--   - reading: total time O(√N/Bmin + 1/ωmin) → one universal C₀ > 0, chosen before W and B_min, bounding reps·(waitMax_i + Σ durations) for every branch i; reason: O(·) uniform in all inputs; p.13 'Each trial takes at most T + D time. Including all waits'
--   - reading: For every B > 0, N ∈ ℕ, there is a protocol … given … a lower bound Bmin ≤ B → the protocol is chosen from (W, B_min) before B, ω and ϕ; reason: Protocol 1's input is W and B_min only (p.12); this is the order the paper proves and the stronger one
--   - reading: detects the signal with error probability at most 1/3 → probability 0 of 'present' under the zero field, and ≥ 2/3 under every signal with B ≥ B_min; reason: p.13: 'the protocol has no false positives and detects a present signal with probability at least 2/3'
--   - generalization: The protocol uses finitely many Pauli Y gates → at most C₀(1 + ω_max N/B_min) Y pulses per trial; reason: the pulse count of p.13 with Theorem 5.13's +1; it implies 'finitely many' and p.4's O(ω_max N/B_min) in the regime ω_min ≥ B_min
--   - reading: 'uses one sensing qubit … Pauli Y gates, alternating with evolution under the signal Hamiltonian'; the paper defines Protocol 1 but no class of protocols → the class Protocol: randomized choice of pulse blocks (start gate, Y pulses between evolutions, finish gate), wait laws on [0, waitMax], fixed repetitions, OR decision, absolute time running across trials; reason: Protocol 1 belongs to the class, and the class allows no dependence on B, ω, ϕ, no ancilla, no adaptivity
--   - encoding: W = {ω1, …, ωN}, N ∈ ℕ → W a nonempty Finset of positive reals, N = |W|; reason: ω_min is undefined for W = ∅
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Theorem 1.1, p.3 (PDF p.3), made precise by Protocol 1 and its 'Success probability' and 'Sensing time and number of pulses' paragraphs, pp.12–13; proved in §§4–7

import Mathlib
import Definitions.Def_QubitFreqSensing_PulseProtocol

namespace QubitFreqSensing

/-- **Theorem 1.1** (Chen, Coladangelo, Li, Zhang, *Sensing frequencies at the discrete
Grover-Heisenberg limit using a single qubit*, manuscript (STOC 2027 submission), Theorem 1.1, p.3,
made precise by Protocol 1 and its "Success probability" and "Sensing time and number of pulses"
paragraphs, pp.12–13). "For every B > 0, N ∈ ℕ, there is a protocol satisfying the following:
given as input a set of candidate frequencies W = {ω1, . . . , ωN}, and a lower bound Bmin ≤ B,
the protocol uses one sensing qubit (and no auxiliary qubits) and detects the signal with error
probability at most 1/3, for every candidate frequency ω ∈ W and every phase ϕ, in total time
O(√N/Bmin + 1/ωmin), where ωmin := mini ωi. The protocol uses finitely many Pauli Y gates,
alternating with evolution under the signal Hamiltonian."

There is a universal `C₀ > 0` such that for every finite nonempty `W ⊂ (0, ∞)` (`N = |W|`) and every
`B_min > 0` there is a single-qubit pulse protocol `P`, depending only on `(W, B_min)`, with
1. worst-case sensing time (all waits and evolutions of all trials) `≤ C₀(√N/B_min + 1/ω_min)`;
2. at most `C₀(1 + ω_max N/B_min)` Pauli-`Y` pulses per trial;
3. no false positives: under the zero field it never outputs "present";
4. for every `B ≥ B_min`, `ω ∈ W` and `ϕ ∈ ℝ`, under the field `B cos(ωt + ϕ)` (absolute time `t`,
   running across trials) it outputs "present" with probability at least `2/3`.

**Formalization Note** The protocol class is `Protocol` (a randomized trial over finitely many
branches, each a wait law supported in `[0, waitMax]` and a pulse block whose only controls are the
start gate, Pauli `Y` pulses between evolutions, and the finish gate; repeated `reps` times; output
"present" iff some outcome is `1`). The `O(·)` is one universal constant `C₀` chosen before `W` and
`B_min`. -/
theorem theorem_1_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (W : Finset ℝ) (hW : W.Nonempty), (∀ ω ∈ W, 0 < ω) → ∀ Bmin : ℝ, 0 < Bmin →
      ∃ P : Protocol,
        (∀ i, (P.reps : ℝ) * (P.trial.waitMax i + (P.trial.block i).durations.sum)
            ≤ C₀ * (Real.sqrt W.card / Bmin + 1 / W.min' hW)) ∧
        (∀ i, ((P.trial.block i).durations.length : ℝ) - 1
            ≤ C₀ * (1 + W.max' hW * W.card / Bmin)) ∧
        presentProb (fun _ => 0) P = 0 ∧
        ∀ B : ℝ, Bmin ≤ B → ∀ ω ∈ W, ∀ ϕ : ℝ,
          2 / 3 ≤ presentProb (fun t => B * Real.cos (ω * t + ϕ)) P := by sorry

end QubitFreqSensing
