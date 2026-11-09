-- Prove2me | Theorems.Thm_RandomQueryXOR_lemma_4_6
-- name    : RandomQueryXOR.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:12:56.155938+00:00
-- url     : https://prove2.me/theorems/3c4960d7-fe9e-4856-8458-91ea9d97ed48
-- title:
--   Lemma 4.6 — two-bit parity game: $I(\Pi;\theta\mid\rho,R_{\rm pub},\alpha,\mathcal E_{\rm eq})=\Omega_\varepsilon(1)$
-- statement:
--   For every $\varepsilon>0$ there is a constant $c(\varepsilon)>0$ such that for every number of players $k$ and every protocol $\pi$ of the two-bit parity game that outputs $\alpha\oplus\beta$ with probability of success at least $1/2+\varepsilon$,
--   $$
--   I\bigl(\Pi\,;\,\theta\ \big|\ \rho,R_{\rm pub},\alpha,\mathcal E_{\rm eq}\bigr)\ \ge\ c(\varepsilon),
--   $$
--   the mutual information being taken under the law of the game conditioned on $\mathcal E_{\rm eq}=\{\alpha=\beta\}$.
--
--   A protocol that computes the parity of two bits, each seen only by players who happen to receive it, must reveal a constant amount about which players received a bit, even on the event where the answer is fixed. Embedded into a branching program for $g_{f\oplus}$, this forces information about the gate bits into the memory.
--
--   Differences from the source:
--   - encoding: Ω_ε(1) → ∃ c > 0 depending only on ε, chosen before k, the alphabets M, R, Q and the protocol; reason: the meaning of Ω_ε(1): a constant depending on ε only
--   - generalization: the last player Q_k writes α ⊕ β → the answer is any function out(R_pub, Π) of the public randomness and the board; reason: Q_k sees R_pub and the whole board, so every printed protocol is one with out decoding its last message
--   - generalization: k ≥ 1 players → any k ∈ ℕ, k = 0 included; reason: for k = 0 the statement holds trivially; it specializes to every k ≥ 1
--   - encoding: a protocol with arbitrary message and randomness spaces → message, public and private randomness on finite types M, R, Q; private coins of each player on a common Q with independent per-player laws; reason: the paper's information theory is on finite sets (Appendix A); player-specific finite alphabets embed into a common one
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Lemma 4.6, p.18 (PDF p.20); proof §5, pp.33–40 (PDF pp.35–42)

import Mathlib
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_TwoBitProtocol

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace

/-- Lemma 4.6 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.18 = PDF p.20): "Let π be a protocol for the two-bit parity game that outputs
α ⊕ β with probability of success at least 1/2 + ε. Then, I(Π ; θ | ρ, R_pub, α, E_eq) = Ω_ε(1)."

**Formalization Note** `Ω_ε(1)` is a constant `c > 0` depending only on `ε`, chosen before the number
of players `k`, the finite alphabets `M, R, Q` and the protocol. The mutual information is under the
law of the game conditioned on `E_eq = {α = β}`. -/
theorem lemma_4_6 : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ (k : ℕ) (M R Q : Type) [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
      [Fintype Q] (π : TwoBitProtocol k M R Q), 1 / 2 + ε ≤ π.success →
      c ≤ cmi (condDist π.gameLaw Eeq) π.transcript theta
        (fun ω => (rho ω, pubR ω, alpha ω)) := by sorry

end RandomQueryXOR
