-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_proposition_5_5
-- name    : SuccinctArgOWF.Kilian.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:52.293257+00:00
-- url     : https://prove2.me/theorems/f9f8615c-580b-4851-84ba-bafcb94506d3
-- title:
--   Proposition 5.5 — the first hybrid step $\Pr[\mathrm{Hyb}_0]-\Pr[\mathrm{Hyb}_1]\le c\cdot\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}_{\mathrm{out}}}(t_\varepsilon)$
-- statement:
--   Let $\mathrm{Com}_{\mathrm{in}}$ be a $c$-round public-coin commitment with interval opening for messages in $\{0,1\}^N$, $c\ge1$, whose sender messages lie in $\{0,1\}^d$ and which has local verification with respect to $J$, let $\mathrm{Com}_{\mathrm{out}}$ be an $\ell$-round public-coin commitment with interval opening for messages in $\{0,1\}^d$, $\ell\ge1$, and let $\mathrm{Com}$ be the scheme of Construction 5.3. Let $V=V(t)$ bound the overhead (sampling and processing the receiver messages of one execution, computing $J(I)$, checking two openings of a time-$t$ adversary), $\varepsilon\in(0,1]$, and $t_\varepsilon=\lfloor C\,c^2(t+V+d)/\varepsilon\rfloor$ for a universal constant $C$.
--
--   For every adversary $A$ of running time $t$ in the selective interval binding game of $\mathrm{Com}$, with the hybrids $\mathrm{Hyb}_0$ (the real game) and $\mathrm{Hyb}_1$ (the two openings must also reveal the same parts $u_i=u'_i$ of all inner messages):
--
--   $$\Pr[\mathrm{Hyb}_0(A)]-\Pr[\mathrm{Hyb}_1(A)]\le c\cdot\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}_{\mathrm{out}}}(t_\varepsilon).$$
--
--   This is the first half of the proof of Lemma 5.4: two accepted openings that reveal different inner restrictions break an outer commitment.
--
--   Differences from the source:
--   - generalization: Com_in and Com_out are commitment schemes (complete, §3.3) → completeness of Com_in, Com_out is not assumed; reason: the binding statement does not use completeness; with it the Lean statement specializes to the source
--   - encoding: t_ε = O(c²(t + V + d)/ε) → t_ε = ⌊C·c²(t + V + d)/ε⌋ with one constant C chosen before the schemes, t, V, ε and A; reason: the O-constant of the source is universal
--   - reading: V = V(t) bounds the overhead of sampling and processing the receiver messages of one execution, computing J(I), and checking two candidate openings, including their revealed inner-message restrictions, for a time-t adversary → a program (machines with advice) whose cost, code plus steps, is at most V for each task: exact uniform sampling of the receiver messages of one execution, computing J(I), and returning both verdicts and both revealed restriction vectors for every output a time-t adversary can produce in the machine model (openings of length at most 2t, messages τ_k of length at most t + |r_k|); reason: makes the informal overhead precise in the cost model
--   - encoding: Ver_in(r⃗, (u_1, …, u_c), I, v, π_in) defined via local verification; (r_i, ρ_{i,1}) sent together → Ver_in evaluated on the messages holding u_i at J(I) and zeros elsewhere, u_i required to have |J(I)| bits; (r_i, ρ_{i,1}) sent as one self-delimiting string; reason: local verification makes the value independent of the padding; Ver_in is only defined for u_i ∈ {0,1}^{|J(I)|}
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Proposition 5.5, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Recursive

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-- Proposition 5.5, Dujmovic–Wichs p.16 (inside the proof of Lemma 5.4). For Construction 5.3 from
`Com_in` (`c ≥ 1` rounds, sender messages in `{0,1}^d`, local verification w.r.t. `J`) and `Com_out`
(`ℓ ≥ 1` rounds, messages in `{0,1}^d`), every `V` bounding the overhead, every `ε ∈ (0,1]` and every
adversary `A` of running time `t`: `Pr[Hyb₀(A)] − Pr[Hyb₁(A)] ≤ c · bind^int_{Com_out}(t_ε)`, with
`t_ε = ⌊C c² (t + V + d)/ε⌋` for a universal constant `C`. -/
theorem proposition_5_5 :
    ∃ C : ℕ, ∀ (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (d : ℕ),
      1 ≤ Ci.ℓ → 1 ≤ Co.ℓ → Co.N = d → Ci.LocalVer d J →
      ∀ t V : ℕ, IsOverheadBound Ci Co J t V → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ A : Adv, A.RunsWithin t [] (Set.range (constr53 Ci Co J).selSched) →
        hybProb Ci Co J 0 A t - hybProb Ci Co J Ci.ℓ A t ≤
          (Ci.ℓ : ℝ) * Co.bindInt (tEps C Ci.ℓ t V d ε) := by sorry

end SuccinctArgOWF.Kilian
