-- Prove2me | Theorems.Thm_VAS5Reach_proposition_6_5
-- name    : VAS5Reach.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:45.737681+00:00
-- url     : https://prove2.me/theorems/c5b1305b-630a-4feb-a715-f0cc70f82849
-- title:
--   Proposition 6.5 — Case II: $\ell_V(s,t) \le (B + \mathrm{SIZE}(V,s,t))^{O(1)}$ for runs of $[\![V]\!]_B$
-- statement:
--   There is a constant $c$ such that the following holds. Let $V$ be a 5-VAS with transition set $T$, $I$ a set of two coordinates, $B \in \mathbb N$, and let $p(x) \xrightarrow{*} q(y)$ in the $B$-encoding $W = [\![V]\!]_{I,B}$, with $s = (p, x)$ and $t = (q, y)$ the corresponding configurations of $V$. Then
--   $$
--   \ell_V(s, t) \le \bigl(B + \mathrm{SIZE}(V, s, t)\bigr)^c . \tag{4}
--   $$
--   In the paper the instance is $(U, p(x), q(y))$ with $U$ the sequential sub-VASS formed by the components traversed by a witnessing run of $W$; together with Theorem 6.1 and Proposition 6.2 it implies Theorem 1.2.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - reading: (U, p(x), q(y)) a reachable instance specified above → p(x) →* q(y) in [[V]]_{I,B}; reason: U is formed by the components traversed by a fixed run of W, so any run determines its U and the bound concerns only V, s, t, B
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: exponent O(1), whose hidden constant is independent of the input (p.25) → one natural-number constant c quantified before every instance; reason: this is the paper's quantifier order; a natural exponent loses nothing because every base is at least 1
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §6.2 and Proposition 6.5, eq. (4), p.27 (PDF p.29)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode

namespace VAS5Reach

/-- **Proposition 6.5.** Let `V` be a 5-VAS and let `(U, p(x), q(y))` be a reachable instance
specified above. Then `ℓ_V(s, t) ≤ (B + SIZE(V, s, t))^{O(1)}` (4).

"Specified above": `W = [[V]]_B` is the `B`-encoding of the 5-VAS `V`, `p(x) −π→ q(y)` is a run in
`W`, `s = (p, x)` and `t = (q, y)`, and `U` is the sequential sub-VASS formed by the SCCs traversed
by `π` together with their connecting transitions.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §6.2, printed p. 27 (PDF p. 29): "Let W = [[V]]_B be the B-encoding of a 5-VAS V, and
fix a run p(x) −π→ q(y) in W, where s = (p, x) and t = (q, y). The SCCs traversed by π, together
with their connecting transitions, form a sequential sub-VASS U", and Proposition 6.5, eq. (4).

**Formalization Note** Since `U` is determined by the witnessing run, the hypothesis is
`p(x) −∗→ q(y)` in `W = [[V]]_{I,B}`. The bound is on `ℓ_V` in the original VAS between
`s = (p, x)` and `t = (q, y)` (the encoded values restored, `decode`), stated as a run of `V` of
length `≤ (B + SIZE(V, s, t))^c` with one `c` quantified first. `I` is any pair of coordinates
(the paper fixes the first two w.l.o.g.). -/
theorem proposition_6_5 :
    ∃ c : ℕ, ∀ (T : Finset (Fin 5 → ℤ)) (I : Finset (Fin 5)) (B : ℕ), I.card = 2 →
      ∀ (p q : Unit × (I → ℕ)) (x y : {i // i ∉ I} → ℕ),
      (encode (VASS.ofVAS T) I B).Reach p x q y →
      ∃ ρ, IsVASRun T (decode I p.2 x) ρ (decode I q.2 y) ∧
        ρ.length ≤ (B + vasSize T (decode I p.2 x) (decode I q.2 y)) ^ c := by sorry

end VAS5Reach
