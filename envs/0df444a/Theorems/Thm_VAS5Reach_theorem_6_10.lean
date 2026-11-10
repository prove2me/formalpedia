-- Prove2me | Theorems.Thm_VAS5Reach_theorem_6_10
-- name    : VAS5Reach.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:07.688282+00:00
-- url     : https://prove2.me/theorems/744bd771-ef77-4d34-8819-a007b47be0b1
-- title:
--   Theorem 6.10 (wide and coverable case) — $\ell_V(s,t) \le (B + C + \mathrm{SIZE}(V,s,t))^{(d+1)^{O(d)}}$ from a $\mathbb Z$-run
-- statement:
--   There is a constant $c$ such that the following holds. Let $V$ be a $(d+2)$-VAS with transition set $T$, $I$ a set of two coordinates, $B \in \mathbb N$, $C$ a transformation-area threshold for $[\![V]\!]_{I,B}$, and $(U, p(x), q(y))$ a sequential sub-VASS of $[\![V]\!]_{I,B}$ whose source and target lie in its first and last components. If $U$ is wide, $(U, p(x), q(y))$ is $C$-coverable, and $p(x) \xrightarrow{*}_{\mathbb Z} q(y)$ in $U$, then, with $s = (p, x)$ and $t = (q, y)$,
--   $$
--   \ell_V(s, t) \le \bigl(B + C + \mathrm{SIZE}(V, s, t)\bigr)^{(d+1)^{c(d+1)}} . \tag{5}
--   $$
--   Only a $\mathbb Z$-run is assumed; the conclusion is a run of $V$.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: exponent (d+1)^{O(d)} → (d + 1)^{c(d+1)} with one constant c quantified before d and every instance; reason: O(d) ≤ c(d + 1) for a suitable c
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.10, eq. (5), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_IsSeqDecomp
import Definitions.Def_VAS5Reach_VASS_FwdCoverable
import Definitions.Def_VAS5Reach_IsTAThreshold
import Definitions.Def_VAS5Reach_VASS_cycleSpace

namespace VAS5Reach

/-- **Theorem 6.10 (Wide and Coverable Case).** Let `V` be a `(d + 2)`-VAS, `B ∈ ℕ`, and
`(U, p(x), q(y))` be a sequential sub-VASS of `[[V]]_B`. Assume that the source and target lie in
the first and last components of `U`, respectively. If `(U, p(x), q(y))` is wide and
`C`-coverable and `p(x) −∗→_Z q(y)` in `U`, then
`ℓ_V(s, t) ≤ (B + C + SIZE(V, s, t))^{(d+1)^{O(d)}}` (5), where `C` is a transformation-area
threshold for `[[V]]_B`, `s = (p, x)` and `t = (q, y)`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.10, eq. (5), printed p. 28 (PDF p. 30).

**Formalization Note** `d + 2 = Fintype.card ι`; the exponent `(d+1)^{O(d)}` is
`(d + 1)^{c(d+1)}` with one `c` quantified before `d` and every instance. The hypothesis is a
`ℤ`-run in `U` (counters cast to `ℤ`), not a run. Wideness is of `U`. The encoded pair `I` is any
two coordinates (the paper fixes the first two w.l.o.g.); `s`, `t` restore the encoded values
(`decode`); `ℓ_V(s, t) ≤ N` is stated as a run of `V` of length `≤ N`. -/
theorem theorem_6_10 :
    ∃ c : ℕ, ∀ (d : ℕ) {ι : Type} [Fintype ι], Fintype.card ι = d + 2 →
      ∀ (T : Finset (ι → ℤ)) (I : Finset ι) (B C : ℕ), I.card = 2 → IsTAThreshold T I B C →
      ∀ (U : VASS (Unit × (I → ℕ)) {i // i ∉ I}) (p q : Unit × (I → ℕ))
        (x y : {i // i ∉ I} → ℕ),
      U.IsSubVASS (encode (VASS.ofVAS T) I B) → U.IsSequential p q →
      U.IsWide → U.Coverable C p x q y →
      U.ZReach p (fun j => (x j : ℤ)) q (fun j => (y j : ℤ)) →
      ∃ ρ, IsVASRun T (decode I p.2 x) ρ (decode I q.2 y) ∧
        ρ.length ≤ (B + C + vasSize T (decode I p.2 x) (decode I q.2 y)) ^ ((d + 1) ^ (c * (d + 1))) := by sorry

end VAS5Reach
