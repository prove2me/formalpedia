-- Prove2me | Theorems.Thm_RobustQSC_proposition_13
-- name    : RobustQSC.proposition_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:24.75196+00:00
-- url     : https://prove2.me/theorems/861012c3-638d-4679-b679-3d2113fe15b0
-- title:
--   Proposition 13, p.49 — local escape property of $A(T)$
-- statement:
--   For any $T\ge12$ there are $\alpha=\alpha(T)>0$ and $\beta=\beta(T)>0$ such that for all $n$ large enough, with probability at least $1-2^{-\beta n}$ over $\mu\sim\boldsymbol\mu$, the set $A=A(T)$ satisfies:
--
--   1. each $x\in\{0,1\}^n$ has at least $\alpha n$ neighbours in $A$;
--   2. for all $x,y$ with $d(x,y)\le3$, at least $\alpha n$ of the $i$-paths $P_i(x,y)$ have all internal vertices in $A$.
--
--   The set of points with near-uniform mass is thus well connected, in spite of the many atypical points of a Porter–Thomas measure.
--
--   Differences from the source:
--   - encoding: "$A$" → $A(T)$ of p.47 for the sampled $\mu$, written `goodSet T μ`; reason: the paper fixes $A$ in the section preamble
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Proposition 13, p.49; §6, p.47; Definition 2, p.48

import Definitions.Def_RobustQSC_dirichletOne
import Definitions.Def_RobustQSC_LocalEscape

namespace RobustQSC

open QAlgorithms MeasureTheory

/-- **Proposition 13 (Local escape property).** For any `T ≥ 12` there are `α = α(T) > 0`,
`β = β(T) > 0` such that for all `n` large enough, with probability at least `1 − 2^{−βn}` over
`μ ∼ 𝛍`, the good set `A = A(T)` has the local escape property: each `x ∈ {0,1}ⁿ` has at least
`αn` neighbours in `A`, and for all `x, y` with `d(x, y) ≤ 3` at least `αn` of the canonical
paths `P_i(x, y)` have all internal vertices in `A`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Proposition 13, p.49; `A(T)`, §6, p.47; Definition 2, p.48.

**Formalization Note.** `μ ∼ 𝛍` is `dirichletOne`; `A(T)` is `goodSet T μ`. -/
theorem proposition_13 :
    ∀ T : ℝ, 12 ≤ T → ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      dirichletOne (Qubits n) {μ | ¬ LocalEscape (goodSet T μ) α}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(β * n))) := by sorry

end RobustQSC
