-- Prove2me | Theorems.Thm_QPVEntanglement_theorem_7_static_verifier_security
-- name    : QPVEntanglement.theorem_7_static_verifier_security
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:11.401351+00:00
-- url     : https://prove2.me/theorems/2f55c851-92c1-4a08-9fb7-a0d60dd44d16
-- title:
--   Theorem 7 — static-verifier security: every winning coalition needs more than $\lfloor m/\lceil\log_2^2\lambda\rceil\rfloor R_H(2\kappa(s-2.5)-1)$ qubits
-- statement:
--   This item is stated in the **operator-requested pinned-down model** of the paper's adversary model (§4, pp.28–29): the paper defines its coalitions only operationally, so the mission fixes a precise model (choices P1–P14 of the mission description) and states the paper's result in it at full strength.
--
--   There is a universal constant $\kappa>0.08$ with the following property. Let $m,R_H,s:\mathbb N\to\mathbb N$ satisfy $s\ge9$, $R_H\ge1$ and $m=\omega(\log_2^2\lambda)$, and put
--
--   $$B(\lambda)=\Big\lfloor\frac{m}{\lceil\log_2^2(\lambda)\rceil}\Big\rfloor R_H\big(2\kappa(s-2.5)-1\big).$$
--
--   1. (24) For all large enough $\lambda$, for every admissible geometry, every schedule and every coalition with no station at the claimed location that is accepted with probability at least $(1-10^{-7})^{\lceil\log_2^2\lambda\rceil}$, its total quantum-register size is strictly greater than $B(\lambda)$. The parameters need not be polynomially bounded.
--   2. (23) If $m,R_H,s$ are polynomially bounded, the protocol has $B(\lambda)$-qubit static-verifier security: for every admissible geometry and every family of schedules and coalitions with no station at the claimed location and size at most $B(\lambda)$, the acceptance probability is bounded by a negligible function of $\lambda$.
--
--   The protocol's honest prover stores $R_H$ qubits and the protocol sends $R_H+2m$ quantum messages, while every successful coalition needs $\Omega(smR_H/\log^2\lambda)$ qubits. Quantifying over every schedule makes the protocol slot-based and inter-slot-delay independent.
--
--   Differences from the source:
--   - reading: adversarial coalition defined operationally (§4 Adversary Model, clauses 1–6, pp.28–29; protocol rules 1–5, pp.30–32) → `Coalition S`: finitely many stations at distinct positions, each with q a qubits and fixed-time events applying a view-dependent complete Kraus instrument and an absorb/launch action, causal w.r.t. the light cone; `acceptProb` and `size` as in the mission description (P5–P11); reason: operator-requested pinned-down model (OPERATOR_NOTE 2026-11-11); the paper's model is not precise enough to state as written
--   - generalization: the protocol's concrete timing (never fixed by the paper), claimed location translated to 0 and reflected (p.36) → every admissible geometry and every schedule satisfying (S1)–(S3), any Δ > 0; reason: quantifying over all specializes to every concrete choice; carries slot-based and inter-slot-delay independence (Definition 3)
--   - encoding: the protocol is slot-based and inter-slot-delay independent → carried by the universal quantifier over every Schedule (slot times τ_k + jΔ, every Δ > 0); reason: Definition 3: slot-based is the form of the schedule; c−Π for every c > 0 is every Δ > 0, which the quantifier covers
--   - generalization: instruction 'challenge, r_k' sent by V_{b_k} to P → visible at every position once it can have arrived at speed 1 from v_{b_k} (both directions), revealing (b_k, i_k, r_k); reason: an adversary on the instruction's path reads it (analysis convention 4, pp.36–37); revealing b_k and i_k gives nothing beyond direction and arrival time; more information for the coalition
--   - generalization: several adversaries possibly at one location → one station per location, acting jointly on all their registers; reason: co-located adversaries may now also exchange quantum states locally; sizes add
--   - generalization: arbitrary classical messages between adversaries → every outcome is visible to every other station at light speed; reason: classical communication is free (clause 6) and a strategy may ignore what it receives
--   - encoding: earlier messages may determine which later operations occur and when; unused operations act as the identity → fixed event times with view-dependent operations that may be the identity; reason: a finite circuit has finitely many possible operation times; an event at each is exact (p.29)
--   - reading: incoming verifier qubits may be kept (swapped into a reset register); no quantum messages between adversaries → a station on the segment can only absorb a carrier (SWAP) exactly when it passes; a carrier cannot be modified and passed on; reason: modify-and-pass would be a quantum message between adversaries (clause 5); a carrier crosses x at most once untouched (p.43)
--   - reading: quantum-register size: qubits of fixed local and outgoing registers, an outgoing register unavailable for reuse until the verifier receives its state → Σ_a q_a, where a launched qubit stays unavailable to its station (no later event acts on it) until it arrives; reason: the launched qubit's register is its outgoing register (p.29); this gives the honest prover R_H qubits as on p.32, and charges no coalition more than the paper does
--   - encoding: the verifiers abort on rejection; responses at the deadline; projection test → no abort announcement, output 1 iff every round passes (footnote 23); arrivals after T_end ignored; responses are single qubits, an extra qubit at a deadline rejects (∃! warranted launch); reason: a strategy reacting to an abort is equivalent on accepting executions; rule 4
--   - reading: for large enough λ → ∃ λ₀ depending only on (m, R_H, s), uniform over geometry, schedule and coalition; reason: the stronger reading; the proof's only thresholds are (5/9)^m < ν(λ) and m ≥ ⌈log₂²λ⌉ (pp.38, 45)
--   - reading: m, R_H, s polynomial functions of λ; m = ω(log₂²λ) → published `PolyBounded` (p λ ≤ (λ+2)^c); m(λ)/log₂²λ → ∞; reason: the weakest reading of 'polynomial' gives the strongest theorem; efficiency is irrelevant to security
--   - generalization: (23) a coalition with fixed locations, protocol with fixed timing → families (S λ, C λ) whose schedule, station number and positions may vary with λ; reason: more coalition families; the fixed-location case is a special case
--   - encoding: (and hence Ω(m/log₂²λ · s R_H)-qubit) → omitted; reason: a consequence of (23) remarked in parentheses, not a separate claim
--   - encoding: negligible function → published `Negligible` (nonnegative, ≤ λ^(−c) eventually for every real c > 0), in an existential; reason: acceptance probabilities are nonnegative, so requiring a nonnegative bound changes nothing
--   - encoding: labels 1 … R_H + m − 1, rounds and slots 1-based; replenishment before each round k > 1 → 0-based labels, rounds, slots; no replenishment after the last round; reason: index shift; a state after the last round is never tested
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 7, eqs. (23)–(24), p.38; proof pp.38–46

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition_size
import Definitions.Def_QPVEntanglement_securityBound
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false

namespace QPVEntanglement

open PPADSIS.SubexpSIS (Negligible PolyBounded)

/-- **Theorem 7 (Static-verifier security of the protocol given in Figure 3)**, p.38, stated in
the operator-requested pinned-down model of §4 (BRIEF P1–P14). Behera–Goyal, *Breaking the
Bounded Entanglement Barrier for Quantum Position Verification*, arXiv:2609.39234 (sha256
bdf2928d…), Theorem 7, eqs. (23)–(24), p.38.

There is a universal constant `κ > 0.08` such that for all parameter functions `m, R_H, s` of
`λ` with `s ≥ 9`, `R_H ≥ 1` and `m = ω(log₂² λ)`, with
`B(λ) = ⌊m/⌈log₂²λ⌉⌋ · R_H · (2κ(s − 2.5) − 1)`:

* (24) there is `λ₀` such that for every `λ ≥ λ₀`, every admissible geometry, every schedule
  and every coalition with no station at the claimed location that succeeds with probability at
  least `(1 − 10⁻⁷)^{⌈log₂²λ⌉}`, its quantum-register size is strictly greater than `B(λ)`
  (arbitrary, not necessarily polynomially bounded parameters);
* (23) if moreover `m, R_H, s` are polynomially bounded, the protocol has `B(λ)`-qubit
  static-verifier security: every family of coalitions (no station at the claimed location) of
  size at most `B(λ)` is accepted with negligible probability.

**Formalization Note.** "Slot-based and inter-slot-delay independent" are carried by the
quantifier over every `Schedule` (the slot times `τ k + jΔ`, every `Δ > 0`; Definition 3). The
proof's constant is `κ = 0.09` (p.45); the statement keeps `∃ κ > 0.08` before all parameters.
`λ₀` depends only on `(m, R_H, s)`, uniformly over geometry, schedule and coalition. In (23) the
geometry is fixed and the schedule, the coalition (and its positions) may vary with `λ`. The
remark "and hence `Ω(m/log₂²λ · sR_H)`-qubit" is a consequence, not a separate clause.
`Negligible`, `PolyBounded` are the published `PPADSIS.SubexpSIS` notions. -/
theorem theorem_7_static_verifier_security :
    ∃ κ : ℝ, 0.08 < κ ∧
      ∀ m RH s : ℕ → ℕ, (∀ lam, 9 ≤ s lam) → (∀ lam, 1 ≤ RH lam) → OmegaLogSq m →
        (∃ lam₀ : ℕ, ∀ lam ≥ lam₀, ∀ (G : Geometry) (S : Schedule G (m lam) (RH lam) (s lam))
            (C : Coalition S), (∀ a, C.pos a ≠ G.x) → nu lam ≤ C.acceptProb →
              securityBound κ m RH s lam < (C.size : ℝ)) ∧
        (PolyBounded m → PolyBounded RH → PolyBounded s →
          ∀ (G : Geometry) (S : (lam : ℕ) → Schedule G (m lam) (RH lam) (s lam))
            (C : (lam : ℕ) → Coalition (S lam)),
            (∀ lam a, (C lam).pos a ≠ G.x) →
            (∀ lam, ((C lam).size : ℝ) ≤ securityBound κ m RH s lam) →
            ∃ negl : ℕ → ℝ, Negligible negl ∧ ∀ lam, (C lam).acceptProb ≤ negl lam) := by sorry

end QPVEntanglement
