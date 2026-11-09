-- Prove2me | Theorems.Thm_RandomQueryXOR_lemma_5_2
-- name    : RandomQueryXOR.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:08:22.231325+00:00
-- url     : https://prove2.me/theorems/d990e960-8810-4bee-988e-9e9aef72c990
-- title:
--   Lemma 5.2 — on a good prefix, information about $(\alpha,\beta)$ reveals information about $\theta_i$
-- statement:
--   Let $\pi$ be a protocol of the two-bit parity game, $i$ a player, and fix a transcript prefix $\Pi_{<i}=p$ and public randomness $R_{\rm pub}=r$ that occur with positive probability. Suppose
--   $$
--   \delta_{uv}:=\Pr\bigl[\alpha=u,\beta=v\ \big|\ \Pi_{<i}=p,\ R_{\rm pub}=r\bigr]\ \ge\ 0.1\qquad\text{for all }u,v\in\{0,1\}.
--   $$
--   Then
--   $$
--   I\bigl(\Pi_i\,;\,\theta_i\ \big|\ \rho_i,\alpha,R_{\rm pub},\Pi_{<i},\mathcal E_{\rm eq}\bigr)\ \ge\ \frac1{64}\,I\bigl(\Pi_i\,;\,\alpha,\beta\ \big|\ \rho_i,R_{\rm pub},\Pi_{<i}\bigr),
--   $$
--   both sides computed for the fixed values $p,r$ (and on $\mathcal E_{\rm eq}=\{\alpha=\beta\}$ on the left).
--
--   Since no player sees both $\alpha$ and $\beta$, a message that changes the distribution of $(\alpha,\beta)$ must depend on whether its sender received a bit, and this remains visible when $\alpha=\beta$.
--
--   Differences from the source:
--   - encoding: fixed Π_{<i} and R_pub → the mutual informations under the law conditioned on the event {Π_{<i} = p, R_pub = r} of positive probability (and E_eq on the left), with conditioning variables ρ_i, α on the left and ρ_i on the right; reason: R_pub and Π_{<i} are constant on that event, so conditioning on them adds nothing
--   - encoding: a protocol with arbitrary message and randomness spaces → message, public and private randomness on finite types M, R, Q; private coins of each player on a common Q with independent per-player laws; reason: the paper's information theory is on finite sets (Appendix A); player-specific finite alphabets embed into a common one
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Lemma 5.2, p.34 (PDF p.36); δ_uv defined on the same page

import Mathlib
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_TwoBitProtocol

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace

/-- Lemma 5.2 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.34 = PDF p.36): "For any fixed prior transcript Π_{<i} and public randomness
R_pub, let δ_{uv} ≥ 0.1 for all u, v ∈ {0, 1}. Then,
I(Π_i ; θ_i | ρ_i, α, R_pub, Π_{<i}, E_eq) ≥ (1/64) · I(Π_i ; α, β | ρ_i, R_pub, Π_{<i})", where
"δ_{uv} := Probability that α = u and β = v conditioned on Π_{<i} = Π_{<i}, R_pub = R_pub".

**Formalization Note** The fixed values are `Π_{<i} = p`, `R_pub = r`, an event of positive
probability. Both sides are mutual informations under the law conditioned on that event (and on
`E_eq` on the left), so `R_pub` and `Π_{<i}` are constant there. Players are 0-based. -/
theorem lemma_5_2 {k : ℕ} {M R Q : Type} [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
    [Fintype Q] (π : TwoBitProtocol k M R Q) (i : Fin k)
    (p : Fin i.val → M) (r : R)
    (hpos : 0 < probOf π.gameLaw fun ω => π.prefixT ω i = p ∧ pubR ω = r)
    (hδ : ∀ u v : Bool, (1 : ℝ) / 10 ≤
      probOf (condDist π.gameLaw fun ω => π.prefixT ω i = p ∧ pubR ω = r)
        (fun ω => alpha ω = u ∧ beta ω = v)) :
    (1 / 64 : ℝ) * cmi (condDist π.gameLaw fun ω => π.prefixT ω i = p ∧ pubR ω = r)
        (fun ω => π.transcript ω i) (fun ω => (alpha ω, beta ω)) (fun ω => rho ω i) ≤
      cmi (condDist π.gameLaw fun ω => (π.prefixT ω i = p ∧ pubR ω = r) ∧ Eeq ω)
        (fun ω => π.transcript ω i) (fun ω => theta ω i) (fun ω => (rho ω i, alpha ω)) := by sorry

end RandomQueryXOR
