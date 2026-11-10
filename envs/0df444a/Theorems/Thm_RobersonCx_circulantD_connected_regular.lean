-- Prove2me | Theorems.Thm_RobersonCx_circulantD_connected_regular
-- name    : RobersonCx.circulantD_connected_regular
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:14.588908+00:00
-- url     : https://prove2.me/theorems/47095842-b92f-4f5f-8311-34c81578a7c9
-- title:
--   §4.1 — $D^{(r)}_n$ is connected and 4-regular
-- statement:
--   Let $r\ge2$ and $n>2r$. The circulant $D^{(r)}_n$ is connected and $4$-regular: every vertex $i$ has exactly the four neighbours $i\pm1$, $i\pm r$.
--
--   Connectivity of $D^{(r)}_q$ gives the "connected" in Theorem 2 and the closure of $\mathrm{Forb}_{\mathrm m}(D^{(r)}_q)$ under disjoint unions.
--
--   Differences from the source:
--   - encoding: 4-regular → every vertex has a neighbour set of `ncard` 4; reason: same notion
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.1, p.8 (PDF p.10), unnumbered

import Mathlib
import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

namespace RobersonCx

/-- §4.1 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), p.8 (PDF p.10)), unnumbered: for `r ≥ 2` and `n > 2r`, `D^(r)_n` "is connected and 4-regular".

**Formalization Note** `r ≥ 2`, `n > 2r` are the standing assumptions of §4.1. Connected is Mathlib's
`Connected`; 4-regular is: every vertex has exactly four neighbours (`neighborSet` has `ncard` 4). -/
theorem circulantD_connected_regular (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    (circulantD n r).Connected ∧ ∀ v : ZMod n, ((circulantD n r).neighborSet v).ncard = 4 := by sorry

end RobersonCx
