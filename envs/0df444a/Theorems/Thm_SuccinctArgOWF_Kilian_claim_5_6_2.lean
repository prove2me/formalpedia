-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_claim_5_6_2
-- name    : SuccinctArgOWF.Kilian.claim_5_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:03.291032+00:00
-- url     : https://prove2.me/theorems/d075cf70-56d4-402b-88a0-85cfaaa16c37
-- title:
--   Claim 5.6.2 — extracted values are consistent: $\Pr[D_i]\le\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}_{\mathrm{out}}}(t_\varepsilon)$
-- statement:
--   Let $\mathrm{Com}_{\mathrm{in}}$ be a $c$-round public-coin commitment with interval opening for messages in $\{0,1\}^N$, $c\ge1$, whose sender messages lie in $\{0,1\}^d$ and which has local verification with respect to $J$, let $\mathrm{Com}_{\mathrm{out}}$ be an $\ell$-round public-coin commitment with interval opening for messages in $\{0,1\}^d$, $\ell\ge1$, and let $\mathrm{Com}$ be the scheme of Construction 5.3. Let $V=V(t)$ bound the overhead (sampling and processing the receiver messages of one execution, computing $J(I)$, checking two openings of a time-$t$ adversary), $\varepsilon\in(0,1]$, and $t_\varepsilon=\lfloor C\,c^2(t+V+d)/\varepsilon\rfloor$ for a universal constant $C$.
--
--   Let $A$ be an adversary of running time $t$ in the selective interval binding game of $\mathrm{Com}$, $Q=\lceil c/\varepsilon\rceil$, and, with the random tape of $A$ fixed, let $D_i$ ($i<c$) be the event that the real execution satisfies $E$ (A wins $\mathrm{Hyb}_1$), some of the $Q$ continuations from the real prefix through outer commitment $i$ satisfies $E$, and the value $\hat u_i$ of the first opening of the first successful continuation differs from the real value $u_i$. Then for every $i\in[c]$ with $i<c$,
--
--   $$\Pr[D_i]\le\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}_{\mathrm{out}}}(t_\varepsilon).$$
--
--   Together with Claim 5.6.1 this bounds the extraction error in Proposition 5.6.
--
--   Differences from the source:
--   - generalization: Com_in and Com_out are commitment schemes (complete, §3.3) → completeness of Com_in, Com_out is not assumed; reason: the binding statement does not use completeness; with it the Lean statement specializes to the source
--   - encoding: t_ε = O(c²(t + V + d)/ε) → t_ε = ⌊C·c²(t + V + d)/ε⌋ with one constant C chosen before the schemes, t, V, ε and A; reason: the O-constant of the source is universal
--   - reading: V = V(t) bounds the overhead of sampling and processing the receiver messages of one execution, computing J(I), and checking two candidate openings, including their revealed inner-message restrictions, for a time-t adversary → a program (machines with advice) whose cost, code plus steps, is at most V for each task: exact uniform sampling of the receiver messages of one execution, computing J(I), and returning both verdicts and both revealed restriction vectors for every output a time-t adversary can produce in the machine model (openings of length at most 2t, messages τ_k of length at most t + |r_k|); reason: makes the informal overhead precise in the cost model
--   - encoding: the reduction A′ of Proposition 5.6 and its trials → the probability space (ω, real receiver coins, Q fresh coin vectors) with D_i defined on it; the first successful trial is the least index whose continuation satisfies E; reason: D_i depends on A′ only through these random choices
--   - encoding: Ver_in(r⃗, (u_1, …, u_c), I, v, π_in) defined via local verification; (r_i, ρ_{i,1}) sent together → Ver_in evaluated on the messages holding u_i at J(I) and zeros elsewhere, u_i required to have |J(I)| bits; (r_i, ρ_{i,1}) sent as one self-delimiting string; reason: local verification makes the value independent of the padding; Ver_in is only defined for u_i ∈ {0,1}^{|J(I)|}
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Claim 5.6.2, p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Recursive

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-- Claim 5.6.2, Dujmovic–Wichs p.18 (inside the proof of Proposition 5.6). In the setting of
Lemma 5.4 (overhead bound `V`, `ε ∈ (0,1]`, `Q = ⌈c/ε⌉`, `t_ε = ⌊C c²(t + V + d)/ε⌋` with a universal
constant `C`), for every adversary `A` of running time `t` and every `i < c` (`i ∈ [c]`):
`Pr[D_i] ≤ bind^int_{Com_out}(t_ε)`. -/
theorem claim_5_6_2 :
    ∃ C : ℕ, ∀ (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (d : ℕ),
      1 ≤ Ci.ℓ → 1 ≤ Co.ℓ → Co.N = d → Ci.LocalVer d J →
      ∀ t V : ℕ, IsOverheadBound Ci Co J t V → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ A : Adv, A.RunsWithin t [] (Set.range (constr53 Ci Co J).selSched) →
      ∀ i : ℕ, 1 ≤ i → i < Ci.ℓ →
        prob (eventD Ci Co J A t (capQ Ci.ℓ ε) i) ≤ Co.bindInt (tEps C Ci.ℓ t V d ε) := by sorry

end SuccinctArgOWF.Kilian
