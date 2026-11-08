-- Prove2me | Theorems.Thm_RoundOptVSS_theorem_8_1
-- name    : RoundOptVSS.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:06:38.681801+00:00
-- url     : https://prove2.me/theorems/15b52c40-7eaf-43b6-83e8-4dda001f6153
-- title:
--   Theorem 8.1 / 1.1 — a (3, 1)-round VSS for $t<n/2$ with perfect privacy, error $2^{-\kappa}$ and polynomial complexity
-- statement:
--   **Theorem 8.1** (Main; informal version Theorem 1.1). There is a verifiable secret sharing protocol with three sharing rounds and one reconstruction round, tolerating $t<n/2$ corruptions, with perfect privacy of the sharing phase, correctness and commitment error $2^{-\kappa}$, and communication and computation polynomial in $n$, $\kappa$ and the secret length $h$.
--
--   Precisely: there is one bit-level protocol $\Pi$ such that
--
--   1. $\Pi$ has communication and computation polynomial in $n,\kappa,h$ (one polynomial for all parameters), and
--   2. for all $n,t$ with $2t<n$, every dealer index, every $\kappa$ and every $h$, $\Pi$ is a VSS (Definition 4.2) with error
--   $$\varepsilon=2^{-\kappa}$$
--   against every static, rushing, computationally unbounded adversary corrupting at most $t$ parties: perfect privacy, and correctness and commitment each with probability at least $1-2^{-\kappa}$.
--
--   By the three-round lower bound of Patra, Choudhary, Rabin and Pandu Rangan, three sharing rounds are necessary, so such a protocol is round-optimal; before this paper every three-round statistical VSS with $t<n/2$ had complexity exponential in $n$.
--
--   **Formalization Note** The (3,1) round structure is fixed by the type of protocols; secrets are bit vectors.
--
--   Differences from the source:
--   - reading: Theorem 8.1: the protocol of Section 8.2 with the WSS of Section 7 and the parameters of Section 8.4 is such a VSS → there exists a bit-level protocol with these properties (Theorem 1.1's form); reason: Theorem 1.1 states existence; the concrete protocol at bit level would put Protocols 3–9 into the goal; it enters through the milestones
--   - reading: secret x ∈ 𝔼^h for a field 𝔼 chosen in §8.4; output in 𝔼^h ∪ {⊥} → secret x ∈ {0,1}^h, output in {0,1}^h ∪ {⊥}; reason: Theorem 1.1 speaks of "the secret length"; bits embed in 𝔼 and outputs outside the embedding decode to ⊥, which preserves correctness, privacy and commitment, with a polynomial change of h
--   - encoding: synchronous model of §4: private authenticated channels, ideal broadcast, static rushing unbounded adversary, a missing or malformed message reads as ⊥ → Protocol / ShareAdv / RecAdv / exec: per-round coins, private messages and one broadcast; the adversary sees honest broadcasts and honest-to-corrupt messages before choosing; inboxes indexed by sender; missing or over-cap messages are none; reason: the model of §4 and p.1
--   - encoding: honest parties sample uniformly from 𝔽^×, 𝒜, 𝔼 → coins are requested moduli N answered by independent uniform values in {0, …, N − 1}; reason: exact uniform sampling from finite sets
--   - reading: "a deterministic function ρ of S … fixed independently of the adversary's reconstruction strategy" → ∀ secret, ∀ sharing adversary, ∃ ρ : (honest view) → Option, ∀ reconstruction adversary; reason: the quantifier order Definition 4.2 states
--   - encoding: S, the honest joint view including local states and the public sharing transcript → the honest parties' inputs, coins and received private and broadcast messages of rounds 0–2; reason: the states are functions of these
--   - encoding: the adversary's view at the end of sharing → the adversary's state after sharing round 2 (an arbitrary type, updated by every rushing step from everything the corrupt parties receive); reason: the adversary that stores its whole observation is among those quantified over, so equality of state laws for every adversary is equality of view laws
--   - generalization: a positive integer h (§4) → every h ∈ ℕ, every dealer index, every κ; reason: h = 0 is a trivial extra case; the statement for h ≥ 1 is a special case
--   - reading: communication and computation polynomial in n, κ and h → one polynomial p before all parameters; all maps PolyTimeComputable; cap, honest states, messages and coin requests of length ≤ p(n + t + κ + h); reason: t < n, so p(n + t + κ + h) is polynomial in n, κ, h
--   - encoding: error at most 2^{−κ} → probabilities ≥ 1 − 2^{−κ} in ℝ≥0∞; reason: same numbers
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Theorem 1.1 (p.2) in the form of Theorem 8.1 (pp.28–29); Definition 4.2 (p.15)

import Mathlib
import Definitions.Def_RoundOptVSS_Model
import Definitions.Def_RoundOptVSS_BitProtocol

open scoped ENNReal

namespace RoundOptVSS

/-- **Theorem 1.1** (Main result), p.2, in the form of **Theorem 8.1** (Main), pp.28–29 of
Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…): there is a verifiable secret
sharing protocol with three sharing rounds and one reconstruction round, tolerating `t < n/2`
corruptions, with perfect privacy of the sharing phase, correctness and commitment error `2^{−κ}`,
and communication and computation polynomial in `n`, `κ` and the secret length `h`.

**Formalization Note.** The protocol is one uniform bit-level protocol (`BitProtocol`) for all
parameters `(n, t, κ, h, dealer)`; its (3, 1) round structure is fixed by the type `Protocol`.
`IsVSS` is Definition 4.2 against every static rushing computationally unbounded adversary with
`|C| ≤ t`, for all `n, t` with `2t < n`, every dealer index, every `κ` and every `h`; the error
is exactly `2^{−κ}`. `Efficient` is the polynomial communication and computation clause, with
one polynomial chosen before every parameter. Secrets are bit vectors `{0,1}^h`. -/
theorem theorem_8_1 :
    ∃ B : BitProtocol, Efficient B ∧ IsVSS B.toProtocol (fun P => ((2 : ℝ≥0∞) ^ P.κ)⁻¹) := by sorry

end RoundOptVSS
