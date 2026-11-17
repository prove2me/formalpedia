-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_b_19
-- name    : PolyContract.Supplement.theorem_b_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:05:28.560174+00:00
-- url     : https://prove2.me/theorems/58ab5aed-3ab0-45bb-b15d-b573b53038e0
-- title:
--   Theorem B.19 — laminar polymatroids: $B\le n+2h(n+1)|\mathcal L|\,3^{h-1}$
-- statement:
--   Let $(f,m,\beta)$ be a valid instance with quadratic costs on $n$ elements, and let $\mathcal L$ be a laminar description of $P^{(+)}(f)$ of height $h$. Then the number $B$ of breakpoints of the best response in $(0,\infty)$ satisfies
--   $$B\le n+2h(n+1)\,|\mathcal L|\,3^{h-1}.$$
--
--   For fixed height this is polynomial in $n$, so the exact algorithm of Theorem 3.7 is efficient on laminar polymatroids of logarithmic height.
--
--   Differences from the source:
--   - encoding: B, the number of breakpoints in (0, ∞) (App. B.8) → every finite set of breakpoints has at most the bound many elements (breakpoints are positive by definition); reason: avoids the cardinality of a possibly infinite set; the breakpoint set is finite (Lemma 3.4)
--   - encoding: 3^{h−1} → integer exponent h − 1; reason: h ≥ 1 on a nonempty ground set; no truncated subtraction
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem B.19, App. B.8.2, p.45 (PDF p.46); App. B.8, p.44

import Mathlib
import Definitions.Def_PolyContract_QuadInstance
import Definitions.Def_PolyContract_Supplement_IsLaminarDescription

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem B.19** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, App. B.8.2, p.45): if `(E, f)` is laminar with a family `L` of height `h`, then
`B ≤ n + 2h(n + 1)|L| 3^{h−1}`, where (in App. B.8, p.44) `B` is the number of breakpoints of `x⋆`
in all of `(0, ∞)`.

**Formalization Note** The instance is a valid quadratic-cost instance on `n = |ι|` elements, `L`
a laminar description of its own polytope `P(+)(f)`, and `h` its height. The bound is stated for
every finite set of breakpoints (each breakpoint is positive by definition), so it bounds their
number in `(0, ∞)`, hence also in `(0, 1)`. The exponent `h − 1` is an integer; `h ≥ 1` holds for
every nonempty ground set, as every element lies in a constraint set. -/
theorem theorem_b_19 {ι : Type} [Fintype ι] [DecidableEq ι] (I : QuadInstance ι) (hI : I.Valid)
    (L : Finset (Finset ι)) (hL : IsLaminarDescription I.f L) (B : Finset ℝ)
    (hB : ∀ b ∈ B, I.IsBreakpoint b) :
    (B.card : ℝ) ≤ Fintype.card ι + 2 * (laminarHeight L : ℝ) * (Fintype.card ι + 1) * L.card *
      (3 : ℝ) ^ ((laminarHeight L : ℤ) - 1) := by sorry

end PolyContract.Supplement
