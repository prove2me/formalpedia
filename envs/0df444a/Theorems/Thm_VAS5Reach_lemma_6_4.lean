-- Prove2me | Theorems.Thm_VAS5Reach_lemma_6_4
-- name    : VAS5Reach.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:44.000044+00:00
-- url     : https://prove2.me/theorems/c5d5a9ee-c59d-4592-9992-78990ec9caea
-- title:
--   Lemma 6.4 — short run from some point of a hybrid source in a 3-VASS of cycle-dimension $\le 2$
-- statement:
--   There is a constant $c$ such that the following holds. Let $V$ be a 3-VASS with $\dim_{\mathrm{cyc}}(V) \le 2$, let $t = q(y)$ be a configuration and $H$ a hybrid set. If $p(x) \xrightarrow{*} t$ for some $x \in H$, then there is $x' \in H$ with
--   $$
--   \|x'\| \le N, \qquad \ell_V(p(x'), t) \le N, \qquad N = \bigl(\mathrm{SIZE}(V, t) + \mathrm{NORM}(H)\bigr)^c,
--   $$
--   where $\mathrm{SIZE}(V, t) = \mathrm{SIZE}(V) + 3(\|y\| + 1)$. This is [CFF+26, Lemma 4.3]; the proof is in the cited work.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - encoding: poly(SIZE(V, t) + NORM(H)) → (SIZE(V, t) + NORM(H))^c with one constant c quantified first; reason: a polynomial is bounded by a power of its argument, which is at least 2
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.4, p.26 (PDF p.28); SIZE(V, s) p.14 (PDF p.16); cited from [CFF+26, Lemma 4.3]

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_VASS_cycleSpace
import Definitions.Def_VAS5Reach_HybridSet

namespace VAS5Reach

/-- **Lemma 6.4 ([CFF+26, Lemma 4.3]).** Let `V` be a 3-VASS with `dimcyc(V) ≤ 2`, `t` be a
configuration, and `H` be a hybrid set. If `p(x) −∗→ t` for some `x ∈ H`, there exists `x′ ∈ H`
with `∥x′∥, ℓ_V(p(x′), t) ≤ poly(SIZE(V, t) + NORM(H))`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.4, printed p. 26 (PDF p. 28); `SIZE(V, t)` as on printed p. 14 (PDF p. 16):
"Sometimes we also consider a pair (V, s) where the target is not fixed; its size SIZE(V, s) is
defined similarly." Cited from [CFF+26, Lemma 4.3]; the proof is not in this paper.

**Formalization Note** `t = q(y)`; `SIZE(V, t) = SIZE(V) + 3·(∥y∥ + 1)` (`size2`). "poly" is
`(SIZE(V, t) + NORM(H))^c` with one `c` quantified first; `ℓ_V(p(x′), t) ≤ N` is stated as a run
of length `≤ N`. -/
theorem lemma_6_4 :
    ∃ c : ℕ, ∀ {ι Q : Type} [Fintype ι] (V : VASS Q ι), Fintype.card ι = 3 → V.dimcyc ≤ 2 →
      ∀ (p q : Q) (y : ι → ℕ) (H : HybridSet ι), (∃ x, H.Mem x ∧ V.Reach p x q y) →
      ∃ x', H.Mem x' ∧ supNormN x' ≤ (V.size2 y + H.norm) ^ c ∧
        ∃ π, V.IsRun p x' π q y ∧ π.length ≤ (V.size2 y + H.norm) ^ c := by sorry

end VAS5Reach
