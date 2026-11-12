-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_claim_5_6_1
-- name    : SuccinctArgOWF.Kilian.claim_5_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:35.903254+00:00
-- url     : https://prove2.me/theorems/9f01229b-ec72-4489-9e45-ac4cf84104cc
-- title:
--   Claim 5.6.1 — capped continuation sampling misses with probability at most $1/(Q+1)$
-- statement:
--   Let $\mathrm{Com}_{\mathrm{in}}$ ($c\ge1$ rounds, interval opening for $\{0,1\}^N$, sender messages in $\{0,1\}^d$, local verification w.r.t. $J$), $\mathrm{Com}_{\mathrm{out}}$ ($\ell\ge1$ rounds, interval opening for $\{0,1\}^d$) and the scheme $\mathrm{Com}$ of Construction 5.3 be as in Lemma 5.4, let $\varepsilon\in(0,1]$, $Q=\lceil c/\varepsilon\rceil$, and let $A$ be an adversary of running time $t$ in the selective interval binding game of $\mathrm{Com}$. Fix the random tape $\omega$ of $A$ across all rewindings, and let $E$ be the event that $A$ wins $\mathrm{Hyb}_1$. For $i<c$, $F_i$ is the event that the real execution satisfies $E$ but all $Q$ independent continuations from the real prefix through outer commitment $i$ (fresh receiver coins afterwards) fail $E$. Then for every $i\in[c]$ with $i<c$,
--
--   $$\Pr[F_i]\le\frac{1}{Q+1}.$$
--
--   This bounds the sampling error of the extraction in Proposition 5.6.
--
--   Differences from the source:
--   - generalization: Com_in and Com_out are commitment schemes (complete, §3.3) → completeness of Com_in, Com_out is not assumed; reason: the binding statement does not use completeness; with it the Lean statement specializes to the source
--   - encoding: the reduction A′ of Proposition 5.6 and its trials → the probability space (ω, real receiver coins, Q fresh coin vectors) with F_i defined on it; only the coins after the real prefix are taken from a trial; reason: F_i depends on A′ only through these random choices
--   - encoding: Ver_in(r⃗, (u_1, …, u_c), I, v, π_in) defined via local verification; (r_i, ρ_{i,1}) sent together → Ver_in evaluated on the messages holding u_i at J(I) and zeros elsewhere, u_i required to have |J(I)| bits; (r_i, ρ_{i,1}) sent as one self-delimiting string; reason: local verification makes the value independent of the padding; Ver_in is only defined for u_i ∈ {0,1}^{|J(I)|}
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Claim 5.6.1, p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Recursive

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-- Claim 5.6.1, Dujmovic–Wichs p.17 (inside the proof of Proposition 5.6). In the setting of
Lemma 5.4, for every adversary `A` of running time `t` against Construction 5.3, every `ε ∈ (0,1]`,
`Q = ⌈c/ε⌉`, and every `i < c` (`i ∈ [c]`): `Pr[F_i] ≤ 1/(Q + 1)`. -/
theorem claim_5_6_1 :
    ∀ (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (d : ℕ),
      1 ≤ Ci.ℓ → 1 ≤ Co.ℓ → Co.N = d → Ci.LocalVer d J →
      ∀ (t : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ A : Adv, A.RunsWithin t [] (Set.range (constr53 Ci Co J).selSched) →
      ∀ i : ℕ, 1 ≤ i → i < Ci.ℓ →
        prob (eventF Ci Co J A t (capQ Ci.ℓ ε) i) ≤ 1 / ((capQ Ci.ℓ ε : ℝ) + 1) := by sorry

end SuccinctArgOWF.Kilian
