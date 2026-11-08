-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_2_6
-- name    : PercCubeCycles.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:17.875217+00:00
-- url     : https://prove2.me/theorems/a22c64d6-c2b5-43fa-9dad-3ad330de0e3c
-- title:
--   Lemma 2.6 — a vertex has a large component or $d^{20}$ near vertices with probability $2\varepsilon+O(\varepsilon^2)$
-- statement:
--   Let $\varepsilon>0$ be sufficiently small, $p=(1+\varepsilon)/d$ and $r\in V(Q^d)$. Then
--   $$\Pr(\text{the component of }r\text{ in }Q^d_p\text{ has at least }\varepsilon^{-6}\text{ vertices})=2\varepsilon+O(\varepsilon^2)$$
--   and
--   $$\Pr(\text{there are at least }d^{20}\text{ vertices at distance at most }\log^2d\text{ from }r\text{ in }Q^d_p)=2\varepsilon+O(\varepsilon^2).$$
--   Here $\log^2d=(\log d)^2$ with the natural logarithm. These are the survival estimates behind the size of the 2-core.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small, $O(\varepsilon^2)$ → $\exists K,\varepsilon_0\ \forall\varepsilon\in(0,\varepsilon_0)$, error at most $K\varepsilon^2$; reason: $K$ precedes $\varepsilon$, so it does not depend on $\varepsilon$
--   - reading: the two probabilities, with "$d$ sufficiently large" as a standing assumption (p.6) → $\exists d_0$ depending on $\varepsilon$, $\forall d\ge d_0$, $\forall r$; reason: the bound is for fixed $\varepsilon$ and large $d$
--   - encoding: vertices at distance at most $\log^2d$ from $r$ → reachable vertices with `dist` at most $(\log d)^2$, including $r$; reason: `dist` is $0$ on unreachable pairs, so reachability is stated
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 2.6, p.8

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Lemma 2.6, p.8, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). For small `ε > 0`, `p = (1 + ε)/d` and `r ∈ V(Q^d)`:
(1) `Pr(the component of r in Q^d_p has at least ε⁻⁶ vertices) = 2ε + O(ε²)`, and
(2) `Pr(there are at least d²⁰ vertices at distance at most log² d from r in Q^d_p) = 2ε + O(ε²)`.

**Formalization Note.** `K` precedes `ε`, and `d` is large given `ε` (the standing assumption, p.6).
`log² d = (Real.log d)²` with the natural logarithm. Vertices at distance at most `log² d` are those
reachable with graph distance at most `log² d`, and `r` itself counts. -/
theorem lemma_2_6 :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ r : Profile d,
      |(percMeasure (supercritical ε d) d {ω | (ε ^ 6)⁻¹ ≤ (compCard ω r : ℝ)}).toReal - 2 * ε|
          ≤ K * ε ^ 2 ∧
      |(percMeasure (supercritical ε d) d {ω |
          ((d : ℝ) ^ 20 ≤ ({u | (openGraph ω).Reachable r u ∧
            ((openGraph ω).dist r u : ℝ) ≤ Real.log d ^ 2} : Set (Profile d)).ncard)}).toReal - 2 * ε|
          ≤ K * ε ^ 2 := by sorry

end PercCubeCycles
