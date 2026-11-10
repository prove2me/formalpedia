-- Prove2me | Theorems.Thm_VAS5Reach_corollary_6_14
-- name    : VAS5Reach.corollary_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:55.345755+00:00
-- url     : https://prove2.me/theorems/fe3358c4-a75a-48cc-b7f2-4d1dc8c359b2
-- title:
--   Corollary 6.14 (coverable case) — $\ell_V(s,t) \le (B + C + \mathrm{SIZE}(V,s,t))^{O(1)}$
-- statement:
--   There is a constant $c$ such that the following holds. Here $V$ is a 5-VAS with transition set $T$, $[\![V]\!]_B$ its $B$-encoding on a pair $I$ of coordinates, $U$ a sequential sub-VASS of $[\![V]\!]_B$ whose source state $p$ lies in its first and target state $q$ in its last component, $C$ a transformation-area threshold for $[\![V]\!]_B$, and $s = (p, x)$, $t = (q, y)$ the configurations of $V$ obtained by restoring the encoded values. If $p(x) \xrightarrow{*} q(y)$ in $U$ and $(U, p(x), q(y))$ is $C$-coverable, then
--   $$
--   \ell_V(s, t) \le \bigl(B + C + \mathrm{SIZE}(V, s, t)\bigr)^c .
--   $$
--   It combines the non-wide bound (Corollary 6.9) with the wide bound (Theorem 6.10).
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - reading: a sequential sub-VASS (U, p(x), q(y)) considered together with its run → IsSequential U p q: p lies in the first and q in the last component of U; reason: the paper's convention for a sequential VASS with a designated run (p.16: its source and target states belong to U1 and Uk)
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: exponent O(1), whose hidden constant is independent of the input (p.25) → one natural-number constant c quantified before every instance; reason: this is the paper's quantifier order; a natural exponent loses nothing because every base is at least 1
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 6.14, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_IsSeqDecomp
import Definitions.Def_VAS5Reach_VASS_FwdCoverable
import Definitions.Def_VAS5Reach_IsTAThreshold

namespace VAS5Reach

/-- **Corollary 6.14 (Coverable Case).** Let `V` be a 5-VAS, `B ∈ ℕ`, and `(U, p(x), q(y))` be a
sequential sub-VASS of `[[V]]_B` such that `p(x) −∗→ q(y)` in `U`. If `(U, p(x), q(y))` is
`C`-coverable, then `ℓ_V(s, t) ≤ (B + C + SIZE(V, s, t))^{O(1)}`, where `C` is a
transformation-area threshold for `[[V]]_B`, `s = (p, x)`, and `t = (q, y)`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 6.14, printed p. 29 (PDF p. 31).

**Formalization Note** The sequential sub-VASS `U` comes with its designated run from `p` to `q`, so by the paper's convention
(printed p. 16) its source state `p` lies in its first and its target state `q` in its last
component (`IsSequential U p q`). The encoded pair `I` is any two coordinates (the paper fixes the
first two w.l.o.g.); `s = (p, x)` and `t = (q, y)` restore the encoded values (`decode`).
`ℓ_V(s, t) ≤ N` is stated as a run of `V` of length `≤ N`; `O(1)` is one constant `c` quantified
before every instance. `C` is any transformation-area threshold for `[[V]]_B` (a hypothesis). -/
theorem corollary_6_14 :
    ∃ c : ℕ, ∀ (T : Finset (Fin 5 → ℤ)) (I : Finset (Fin 5)) (B C : ℕ), I.card = 2 →
      IsTAThreshold T I B C →
      ∀ (U : VASS (Unit × (I → ℕ)) {i // i ∉ I}) (p q : Unit × (I → ℕ))
        (x y : {i // i ∉ I} → ℕ),
      U.IsSubVASS (encode (VASS.ofVAS T) I B) → U.IsSequential p q →
      U.Reach p x q y → U.Coverable C p x q y →
      ∃ ρ, IsVASRun T (decode I p.2 x) ρ (decode I q.2 y) ∧
        ρ.length ≤ (B + C + vasSize T (decode I p.2 x) (decode I q.2 y)) ^ c := by sorry

end VAS5Reach
