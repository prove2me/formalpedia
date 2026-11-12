-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_composition_theorem
-- name    : SuccinctArgOWF.Kilian.composition_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:43.590769+00:00
-- url     : https://prove2.me/theorems/0389053d-a39e-4ee3-a9d2-15483f09fa35
-- title:
--   Theorem 5.2 — composition preserves selective interval binding
-- statement:
--   Let $c,\ell\ge1$, let $\mathrm{Com}_{\mathrm{in}}$ be a $c$-round public-coin commitment scheme with interval opening for messages in $\{0,1\}^N$ whose sender messages lie in $\{0,1\}^d$ and which has local verification with respect to $J$, and let $\mathrm{Com}_{\mathrm{out}}$ be an $\ell$-round public-coin commitment scheme with interval opening for messages in $\{0,1\}^d$ in which the committer sends $s$ bits. Let $\mathrm{Com}$ be the scheme of Construction 5.3. Then:
--
--   1. $\mathrm{Com}$ is a $c\ell$-round public-coin commitment scheme with interval opening for messages in $\{0,1\}^N$ in which the committer sends $cs$ bits, complete when $\mathrm{Com}_{\mathrm{in}}$ and $\mathrm{Com}_{\mathrm{out}}$ are;
--   2. for every $t$, every $V=V(t)$ bounding the overhead (sampling and processing the receiver messages of one execution, computing $J(I)$, checking two candidate openings with their revealed inner restrictions, for a time-$t$ adversary) and every $\varepsilon\in(0,1]$,
--
--   $$\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}}(t)\le\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}_{\mathrm{in}}}(t_\varepsilon)+2c\cdot\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}_{\mathrm{out}}}(t_\varepsilon)+\varepsilon,\qquad t_\varepsilon=\Bigl\lfloor\frac{C\,c^2(t+V+d)}{\varepsilon}\Bigr\rfloor$$
--
--   for a universal constant $C$;
--   3. an opening of an interval $I$ consists of an opening of $\mathrm{Com}_{\mathrm{in}}$ on $I$ and $c$ openings of $\mathrm{Com}_{\mathrm{out}}$ on $J(I)$;
--   4. if $\mathrm{Com}_{\mathrm{out}}$ has local verification with respect to $J_{\mathrm{out}}$, then $\mathrm{Com}$ has local verification with respect to $I\mapsto J_{\mathrm{out}}(J(I))$ (stated after Construction 5.3), so the construction can be applied recursively.
--
--   This is the recursion step of the Merkle-tree-like vector commitment of Corollary 6.3.
--
--   Differences from the source:
--   - generalization: there exists a cℓ-round scheme Com → the scheme of Construction 5.3 (the paper's proof instantiates it); reason: a specific witness implies the existence claim
--   - encoding: the committer of Com_out sends s bits → exactly s bits on every message in {0,1}^d and all coins; reason: the source's count
--   - generalization: Com_in and Com_out are commitment schemes (complete) → completeness assumed only for the completeness clause; reason: the other clauses do not use it
--   - encoding: t_ε = O(c²(t + V + d)/ε) → t_ε = ⌊C·c²(t + V + d)/ε⌋ with one constant C chosen before the schemes, t, V, ε and A; reason: the O-constant of the source is universal
--   - reading: V = V(t) bounds the overhead of sampling and processing the receiver messages of one execution, computing J(I), and checking two candidate openings, including their revealed inner-message restrictions, for a time-t adversary → a program (machines with advice) whose cost, code plus steps, is at most V for each task: exact uniform sampling of the receiver messages of one execution, computing J(I), and returning both verdicts and both revealed restriction vectors for every output a time-t adversary can produce in the machine model (openings of length at most 2t, messages τ_k of length at most t + |r_k|); reason: makes the informal overhead precise in the cost model
--   - encoding: Ver_in(r⃗, (u_1, …, u_c), I, v, π_in) defined via local verification; (r_i, ρ_{i,1}) sent together → Ver_in evaluated on the messages holding u_i at J(I) and zeros elsewhere, u_i required to have |J(I)| bits; (r_i, ρ_{i,1}) sent as one self-delimiting string; reason: local verification makes the value independent of the padding; Ver_in is only defined for u_i ∈ {0,1}^{|J(I)|}
--   - generalization: Theorem 5.2 as printed → adds clause 4 (local verification of Com w.r.t. I ↦ J_out(J(I))), shown after Construction 5.3; reason: Corollary 6.3 applies the construction recursively; extra conclusion clause
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Theorem 5.2, p. 13 (PDF p. 15); local verification of Construction 5.3, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Recursive

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-- Theorem 5.2 (composition), Dujmovic–Wichs p.13, for the scheme `Com` of Construction 5.3 built
from `Com_in` (`c ≥ 1` rounds, interval opening for `{0,1}^N`, sender messages in `{0,1}^d`, local
verification w.r.t. `J`) and `Com_out` (`ℓ ≥ 1` rounds, interval opening for `{0,1}^d`, committer
sends `s` bits): `Com` has `cℓ` rounds, its committer sends `cs` bits, it is complete when `Com_in`
and `Com_out` are, for every overhead bound `V = V(t)` and `ε ∈ (0,1]`
`bind^int_Com(t) ≤ bind^int_{Com_in}(t_ε) + 2c · bind^int_{Com_out}(t_ε) + ε` with
`t_ε = ⌊C c²(t + V + d)/ε⌋` (`C` universal), an opening of `I` consists of an opening of `Com_in` on
`I` and `c` openings of `Com_out` on `J(I)`, and (text after Construction 5.3) `Com` has local
verification w.r.t. `I ↦ J_out(J(I))` whenever `Com_out` has local verification w.r.t. `J_out`. -/
theorem composition_theorem :
    ∃ C : ℕ, ∀ (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (d s : ℕ),
      1 ≤ Ci.ℓ → 1 ≤ Co.ℓ → Co.N = d → Ci.LocalVer d J → Co.SenderBits s →
        (constr53 Ci Co J).ℓ = Ci.ℓ * Co.ℓ ∧
        (constr53 Ci Co J).SenderBits (Ci.ℓ * s) ∧
        (Ci.Complete → Co.Complete → (constr53 Ci Co J).Complete) ∧
        (∀ t V : ℕ, IsOverheadBound Ci Co J t V → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          (constr53 Ci Co J).bindInt t ≤
            Ci.bindInt (tEps C Ci.ℓ t V d ε) + 2 * (Ci.ℓ : ℝ) * Co.bindInt (tEps C Ci.ℓ t V d ε) +
              ε) ∧
        (∀ (st : Ci.σ × (ℕ → Str) × (ℕ → Co.σ)) (a b : ℕ), (constr53 Ci Co J).Open st a b =
          encList [Ci.Open st.1 a b, encList ((List.range Ci.ℓ).flatMap fun i =>
            [sub (st.2.1 i) (J a b).1 (J a b).2, Co.Open (st.2.2 i) (J a b).1 (J a b).2])]) ∧
        (∀ (dout : ℕ) (Jout : ℕ → ℕ → ℕ × ℕ), Co.LocalVer dout Jout →
          (constr53 Ci Co J).LocalVer dout fun a b => Jout (J a b).1 (J a b).2) := by sorry

end SuccinctArgOWF.Kilian
