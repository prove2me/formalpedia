-- Prove2me | Theorems.Thm_PercCubeCycles_theorem_2
-- name    : PercCubeCycles.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:45.436758+00:00
-- url     : https://prove2.me/theorems/fac1ce0d-a77f-4db7-93c0-a8c02f9c4259
-- title:
--   Theorem 2 — the 2-core of the giant has size $(2\varepsilon^2+O(\varepsilon^3))2^d$
-- statement:
--   Let $\varepsilon>0$ be sufficiently small and $p=(1+\varepsilon)/d$. Whp the 2-core of the giant component of $Q^d_p$ has size
--   $$(2\varepsilon^2+O(\varepsilon^3))2^d.$$
--   Since every cycle lies in the 2-core, this gives the matching upper bound for the circumference.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small, $O(\varepsilon^3)$ → $\exists K,\varepsilon_0\ \forall\varepsilon\in(0,\varepsilon_0)$, error at most $K\varepsilon^3$; reason: $K$ precedes $\varepsilon$, so it does not depend on $\varepsilon$
--   - reading: the giant component $L_1$ → every vertex set of a largest component; reason: the page assumes a unique giant; the statement for every largest component covers ties and is not the weaker reading
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Theorem 2, p.3

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Theorem 2, p.3, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). For small `ε > 0` and `p = (1 + ε)/d`, whp the 2-core of the giant component
of `Q^d_p` has size `(2ε² + O(ε³))2^d`.

**Formalization Note.** `K` precedes `ε`. The giant is every largest component. -/
theorem theorem_2 :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) fun d ω => ∀ L₁, IsLargestComponent (openGraph ω) L₁ →
        |((twoCore (restrict (openGraph ω) L₁)).card : ℝ) - 2 * ε ^ 2 * 2 ^ d|
          ≤ K * ε ^ 3 * 2 ^ d := by sorry

end PercCubeCycles
