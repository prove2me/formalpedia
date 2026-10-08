-- Prove2me | Theorems.Thm_VeinottNoDiscount_Overtake_theorem_7
-- name    : VeinottNoDiscount.Overtake.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:05.026198+00:00
-- url     : https://prove2.me/theorems/8b97091c-2d26-43df-9781-96afd65d4aab
-- title:
--   Theorem 7 — f ∈ F″ iff lim_{N→∞} N⁻¹ Σ_{n=1}^N [Vⁿ(f^∞) − Vⁿ(g^∞)] ≧ 0 for all g ∈ F
-- statement:
--   In the finite decision model, let $F''$ be the set of decision rules $f$ that maximize the gain $x(f)$ coordinatewise over all decision rules and then, among the gain maximizers, maximize the bias $y(f)$. For a decision rule $g$ let $V^n(g^\infty)$ be the vector of total expected returns in periods $1,\dots,n$ under the stationary policy $g^\infty$. Then $f\in F''$ if and only if, for every decision rule $g\in F$,
--   $$\lim_{N\to\infty}\frac1N\sum_{n=1}^{N}\bigl[V^n(f^\infty)-V^n(g^\infty)\bigr]\ \ge\ 0,$$
--   coordinatewise, where the limit is taken in the extended reals $[-\infty,+\infty]$.
--
--   The theorem characterizes the stationary policies that are 1-optimal (equivalently, maximize gain and then bias) by an undiscounted criterion: the Cesàro averages of their finite-horizon returns are, in the limit, at least those of every other stationary policy.
--
--   **Formalization Note** For each $g$ and each state $s$, the statement asserts that the real sequence $N^{-1}\sum_{n=1}^N[V^n(f^\infty)-V^n(g^\infty)]_s$, viewed in the extended reals, converges to some limit $L\in[-\infty,+\infty]$ with $L\ge0$; the limit may be $+\infty$ (when $x(f)_s>x(g)_s$). The comparison class is the stationary policies $g^\infty$ only, as in the paper. The $N=0$ term, where Lean sets $0^{-1}=0$, does not affect the limit.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1294, Theorem 7

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Overtake_Criteria
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Overtake

/-- **Theorem 7.** `f ε F″` if and only if
`lim_{N→∞} N⁻¹ Σ_{n=1}^N [V^n(f^∞) − V^n(g^∞)] ≧ 0` for all `g ε F`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1294, Theorem 7.

**Formalization Note.** The vector inequality is read coordinatewise (`∀ s`). By (28) the
averaged difference at state `s` is `[(N + 1)/2](x(f) − x(g))_s + (y(f) − y(g))_s + o(1)`,
which tends to `+∞` or `−∞` when `x(f)_s ≠ x(g)_s`; so "lim … ≧ 0" is a limit in the
extended reals `[−∞, +∞]`. It is stated literally: for every `g` and `s` the real sequence,
cast to `EReal`, converges to some `L : EReal` with `0 ≤ L` (`L = +∞` allowed). Since that
limit always exists, this is equivalent to `lim inf ≧ 0`. The comparison class is the
stationary policies `g^∞`, `g ε F = St → Act`, as printed. The `N = 0` term (`0⁻¹ = 0` in
Lean) does not affect the limit. -/
theorem theorem_7 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    f ∈ VeinottNoDiscount.Improve.Fdprime M ↔
      ∀ g : St → Act, ∀ s : St, ∃ L : EReal,
        Tendsto (fun N : ℕ => ((((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            (Vn M (Policy.stationary f) n s - Vn M (Policy.stationary g) n s)) : ℝ) : EReal))
          atTop (𝓝 L) ∧ 0 ≤ L := by sorry

end VeinottNoDiscount.Overtake
