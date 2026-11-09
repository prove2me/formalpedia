-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_5_4
-- name    : RandomQueryXOR.claim_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:10:41.443222+00:00
-- url     : https://prove2.me/theorems/6b0fb00b-2a34-48ee-a365-c9bc44f5264b
-- title:
--   Claim 5.4 — $\pi_{\rm bad}$ reveals $\Omega_\varepsilon(1)$ information about $(\alpha,\beta)$
-- statement:
--   For every $0<\varepsilon<1/2$ there is a constant $c(\varepsilon)>0$ such that for every number of players $k$ and every protocol $\pi$ of the two-bit parity game that outputs $\alpha\oplus\beta$ with probability at least $1/2+\varepsilon$, the truncated protocol $\pi_{\rm bad}$ satisfies
--   $$
--   I\bigl(\Pi_{\rm bad}\,;\,\alpha,\beta\ \big|\ R_{\rm pub}\bigr)\ \ge\ c(\varepsilon).
--   $$
--
--   Either many transcripts already reach a prefix that has revealed a constant amount about $(\alpha,\beta)$, or $\pi_{\rm bad}$ is close to $\pi$ and inherits its advantage; in both cases its transcript carries constant information. This is the step that lets Lemma 5.2 be applied only on good prefixes.
--
--   Differences from the source:
--   - reading: for any ε < 1/2 (π a protocol of Lemma 4.6) → for 0 < ε < 1/2 and every protocol π with success probability at least 1/2 + ε; reason: the claim is stated inside the proof of Lemma 4.6, whose protocol has this success; the proof uses it (p.39)
--   - encoding: Ω_ε(1) → ∃ c > 0 depending only on ε, chosen before k, the alphabets M, R, Q and the protocol; reason: the meaning of Ω_ε(1): a constant depending on ε only
--   - generalization: the last player Q_k writes α ⊕ β → the answer is any function out(R_pub, Π) of the public randomness and the board; reason: Q_k sees R_pub and the whole board, so every printed protocol is one with out decoding its last message
--   - generalization: k ≥ 1 players → any k ∈ ℕ, k = 0 included; reason: for k = 0 the statement holds trivially; it specializes to every k ≥ 1
--   - encoding: a protocol with arbitrary message and randomness spaces → message, public and private randomness on finite types M, R, Q; private coins of each player on a common Q with independent per-player laws; reason: the paper's information theory is on finite sets (Appendix A); player-specific finite alphabets embed into a common one
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 5.4, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_TwoBitProtocol
import Definitions.Def_RandomQueryXOR_piBad

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace TwoBitProtocol

/-- Claim 5.4 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.38 = PDF p.40): "For any ε < 1/2, the protocol π_bad reveals constant
information about α, β. I(Π_bad ; α, β | R_pub) = Ω_ε(1)."

**Formalization Note** `π_bad` is built from a protocol `π` of Lemma 4.6, so the hypothesis that `π`
succeeds with probability at least `1/2 + ε`, `ε > 0`, is made explicit (the proof uses it, p.39).
`Ω_ε(1)` is a constant `c > 0` depending only on `ε`: it is chosen before the number of players `k`,
the finite alphabets `M, R, Q` and the protocol. -/
theorem claim_5_4 : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ c : ℝ, 0 < c ∧
    ∀ (k : ℕ) (M R Q : Type) [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
      [Fintype Q] (π : TwoBitProtocol k M R Q), 1 / 2 + ε ≤ π.success →
      c ≤ cmi π.piBad.gameLaw π.piBad.transcript (fun ω => (alpha ω, beta ω)) pubR := by sorry

end RandomQueryXOR
