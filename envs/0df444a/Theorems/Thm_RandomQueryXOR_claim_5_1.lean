-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_5_1
-- name    : RandomQueryXOR.claim_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:09:56.64668+00:00
-- url     : https://prove2.me/theorems/63045340-5215-45ba-98f0-b75a10f83abd
-- title:
--   Claim 5.1 — the transcript's information about $\theta$ separates into individual players
-- statement:
--   For every protocol $\pi$ of the two-bit parity game with $k$ players,
--   $$
--   I\bigl(\Pi\,;\,\theta\ \big|\ \rho,R_{\rm pub},\alpha,\mathcal E_{\rm eq}\bigr)\ \ge\ \sum_{i\in[k]} I\bigl(\Pi_i\,;\,\theta_i\ \big|\ \rho_i,R_{\rm pub},\alpha,\Pi_{<i},\mathcal E_{\rm eq}\bigr),
--   $$
--   where all mutual informations are taken under the law of the game conditioned on $\mathcal E_{\rm eq}=\{\alpha=\beta\}$, the left side conditions on the whole vector $\rho$ and the $i$-th term on $\rho_i$ only.
--
--   This direct-sum step reduces the lower bound of Lemma 4.6 to the information each player's own message reveals about its own $\theta_i$.
--
--   Differences from the source:
--   - encoding: a protocol with arbitrary message and randomness spaces → message, public and private randomness on finite types M, R, Q; private coins of each player on a common Q with independent per-player laws; reason: the paper's information theory is on finite sets (Appendix A); player-specific finite alphabets embed into a common one
--   - generalization: k ≥ 1 players → any k ∈ ℕ, k = 0 included; reason: for k = 0 the statement holds trivially; it specializes to every k ≥ 1
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 5.1, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_TwoBitProtocol

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace

/-- Claim 5.1 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.34 = PDF p.36): "For any protocol π,
I(Π ; θ | ρ, R_pub, α, E_eq) ≥ ∑_{i∈[k]} I(Π_i ; θ_i | ρ_i, R_pub, α, Π_{<i}, E_eq)."

**Formalization Note** All mutual informations are under the law of the game conditioned on
`E_eq = {α = β}`; the left side conditions on the whole vector `ρ`, each right-hand term on `ρ_i`
only. Players are 0-based. -/
theorem claim_5_1 {k : ℕ} {M R Q : Type} [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
    [Fintype Q] (π : TwoBitProtocol k M R Q) :
    ∑ i : Fin k, cmi (condDist π.gameLaw Eeq) (fun ω => π.transcript ω i) (fun ω => theta ω i)
        (fun ω => (rho ω i, pubR ω, alpha ω, π.prefixT ω i)) ≤
      cmi (condDist π.gameLaw Eeq) π.transcript theta (fun ω => (rho ω, pubR ω, alpha ω)) := by sorry

end RandomQueryXOR
