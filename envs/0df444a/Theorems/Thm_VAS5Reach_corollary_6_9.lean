-- Prove2me | Theorems.Thm_VAS5Reach_corollary_6_9
-- name    : VAS5Reach.corollary_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:27.345445+00:00
-- url     : https://prove2.me/theorems/bb4ddc29-dec5-4d66-9ffd-6c3f193013dc
-- title:
--   Corollary 6.9 (non-wide case) — $\ell_U(s,t) \le \mathrm{SIZE}(U,s,t)^{O(1)}$ for 3-VASS with $\mathrm{cone}(U) \ne \mathbb Q^3$
-- statement:
--   There is a constant $c$ such that every reachable 3-VASS instance $(U, s, t)$ with $\mathrm{cone}(U) \ne \mathbb Q^3$ satisfies
--   $$
--   \ell_U(s, t) \le \mathrm{SIZE}(U, s, t)^c .
--   $$
--   The distance is measured in $U$ itself.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - encoding: exponent O(1), whose hidden constant is independent of the input (p.25) → one natural-number constant c quantified before every instance; reason: this is the paper's quantifier order; a natural exponent loses nothing because every base is at least 1
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 6.9, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_VAS5Reach_VASS
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_VASS_cycleSpace

namespace VAS5Reach

/-- **Corollary 6.9.** Let `(U, s, t)` be a reachable 3-VASS with `cone(U) ≠ ℚ³`. Its reachability
distance satisfies `ℓ_U(s, t) ≤ SIZE(U, s, t)^{O(1)}`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 6.9, printed p. 27 (PDF p. 29); `cone(U)`: Definition 6.6, same page.

**Formalization Note** `cone(U) ≠ ℚ³` is `¬ U.IsWide`. `s = p(x)`, `t = q(y)`; the distance is in
`U` itself, stated as a run of `U` of length `≤ SIZE(U, s, t)^c` with one `c` quantified first. -/
theorem corollary_6_9 :
    ∃ c : ℕ, ∀ {ι Q : Type} [Fintype ι] (U : VASS Q ι), Fintype.card ι = 3 → ¬ U.IsWide →
      ∀ (p q : Q) (x y : ι → ℕ), U.Reach p x q y →
      ∃ π, U.IsRun p x π q y ∧ π.length ≤ U.size3 x y ^ c := by sorry

end VAS5Reach
