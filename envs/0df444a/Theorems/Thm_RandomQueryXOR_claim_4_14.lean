-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_4_14
-- name    : RandomQueryXOR.claim_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:11:28.450601+00:00
-- url     : https://prove2.me/theorems/fe9ac6a2-09ec-43a7-92c0-0add2ed91950
-- title:
--   Claim 4.14 — $I(\Pi;\theta\mid\dots)\le\sum_a\sum_{c\le a} I(\Pi_a;\theta_c\mid\Pi_{<c},\dots)$
-- statement:
--   For every protocol of the two-bit parity game with $k$ players and transcript $\Pi=(\Pi_1,\dots,\Pi_k)$,
--   $$
--   I\bigl(\Pi\,;\,\theta\ \big|\ \rho,R_{\rm pub},\alpha,\mathcal E_{\rm eq}\bigr)\ \le\ \sum_{a=1}^{k}\ \sum_{c=1}^{a} I\bigl(\Pi_a\,;\,\theta_c\ \big|\ \Pi_{<c},\rho,R_{\rm pub},\alpha,\mathcal E_{\rm eq}\bigr),
--   $$
--   all terms under the law conditioned on $\mathcal E_{\rm eq}=\{\alpha=\beta\}$. Note that the $(a,c)$ term conditions on the prefix $\Pi_{<c}$ before player $c$.
--
--   Applied to $\pi_{\rm two}$ (whose public randomness is $R^{\rm two}_{\rm pub}$), this rewrites the external information as a sum over pairs of a message and an earlier player's bit, which Lemma 4.16 matches with pairs of times in the information cost.
--
--   Differences from the source:
--   - generalization: the transcript Π^two of π_two with public randomness R^two_pub → every protocol of the two-bit parity game; reason: the proof uses only the protocol structure; π_two is an instance
--   - generalization: k ≥ 1 players → any k ∈ ℕ, k = 0 included; reason: for k = 0 the statement holds trivially; it specializes to every k ≥ 1
--   - encoding: a protocol with arbitrary message and randomness spaces → message, public and private randomness on finite types M, R, Q; private coins of each player on a common Q with independent per-player laws; reason: the paper's information theory is on finite sets (Appendix A); player-specific finite alphabets embed into a common one
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 4.14, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_TwoBitProtocol

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace

/-- Claim 4.14 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.23 = PDF p.25): "For any protocol with transcript Π^two_a by Q_a,
I(Π^two ; θ | ρ, R^two_pub, α, E_eq) ≤ ∑_{a=1}^{k} ∑_{c=1}^{a} I(Π^two_a ; θ_c | Π^two_{<c}, ρ, R^two_pub, α, E_eq)."

**Formalization Note** Stated for every protocol of the two-bit parity game (the proof uses only the
protocol structure); π_two is an instance. Players are 0-based; the conditioning is on `Π_{<c}`, not
`Π_{<a}`. -/
theorem claim_4_14 {k : ℕ} {M R Q : Type} [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
    [Fintype Q] (π : TwoBitProtocol k M R Q) :
    cmi (condDist π.gameLaw Eeq) π.transcript theta (fun ω => (rho ω, pubR ω, alpha ω)) ≤
      ∑ a : Fin k, ∑ c ∈ Finset.univ.filter (fun c : Fin k => c ≤ a),
        cmi (condDist π.gameLaw Eeq) (fun ω => π.transcript ω a) (fun ω => theta ω c)
          (fun ω => (π.prefixT ω c, rho ω, pubR ω, alpha ω)) := by sorry

end RandomQueryXOR
