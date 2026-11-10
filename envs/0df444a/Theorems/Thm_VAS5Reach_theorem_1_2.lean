-- Prove2me | Theorems.Thm_VAS5Reach_theorem_1_2
-- name    : VAS5Reach.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:31.587893+00:00
-- url     : https://prove2.me/theorems/6d760d91-613c-40ca-8e97-de5e89271e78
-- title:
--   Theorem 1.2 (polynomial reachability distance) — every reachable 5-VAS instance has a run of length $\le \mathrm{SIZE}(V,s,t)^c$
-- statement:
--   There exists a constant $c$ such that for every reachable 5-VAS instance $(V, s, t)$ — a finite set $T \subseteq \mathbb Z^5$ of transitions and configurations $s, t \in \mathbb N^5$ with $s \xrightarrow{*} t$ — one has
--   $$
--   \ell_V(s, t) \le \mathrm{SIZE}(V, s, t)^c ,
--   $$
--   where $\ell_V(s, t)$ is the least length of a run from $s$ to $t$ (all intermediate configurations in $\mathbb N^5$) and
--   $$
--   \mathrm{SIZE}(V, s, t) = 1 + 5\,|T|\,(\|T\| + 1) + 2 + 5\,(\|s\| + \|t\| + 1)
--   $$
--   is the unary size of the instance, $\|\cdot\|$ the max norm and $\|T\| = \max_{a \in T} \|a\|$.
--
--   A nondeterministic machine can guess a run of length at most $\mathrm{SIZE}(V,s,t)^c$ using logarithmic space, which gives the NL (unary) and PSPACE (binary) upper bounds of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - encoding: a constant c → c : ℕ quantified before every instance; reason: SIZE(V, s, t) ≥ 2, so a real exponent can be rounded up to a natural one
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.2, p.2 (PDF p.4); restated App. D.2, p.49 (PDF p.51); SIZE p.14 (PDF p.16), ℓ_V p.15 (PDF p.17)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_vasSize

namespace VAS5Reach

/-- **Theorem 1.2 (Polynomial Reachability Distance).** There exists a constant `c` such that for
every reachable 5-VAS instance `(V, s, t)`, one has `ℓ_V(s, t) ≤ SIZE(V, s, t)^c`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.2, printed p. 2 (PDF p. 4); restated in App. D.2, printed p. 49
(PDF p. 51). Size: §3, printed p. 14 (PDF p. 16); distance: printed p. 15 (PDF p. 17).

**Formalization Note** A 5-VAS is a finite set `T ⊆ ℤ⁵`; configurations are vectors of `ℕ⁵`.
`ℓ_V(s, t) := min LEN(V, s, t)` is the least length of a run from `s` to `t`; with `t`
reachable from `s`, `ℓ_V(s, t) ≤ N` is the same as "some run from `s` to `t` has length
`≤ N`", which is what is stated (no minimum is formed). `SIZE(V, s, t) = 1 + 5·|T|·(∥T∥ + 1) + 2 +
5·(∥s∥ + ∥t∥ + 1)` exactly as printed (`vasSize`). The constant `c` is quantified before every
instance. -/
theorem theorem_1_2 :
    ∃ c : ℕ, ∀ (T : Finset (Fin 5 → ℤ)) (s t : Fin 5 → ℕ), VASReach T s t →
      ∃ w : List (Fin 5 → ℤ), IsVASRun T s w t ∧ w.length ≤ vasSize T s t ^ c := by sorry

end VAS5Reach
