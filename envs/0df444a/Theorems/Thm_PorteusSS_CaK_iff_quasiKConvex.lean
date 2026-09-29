-- Prove2me | Theorems.Thm_PorteusSS_CaK_iff_quasiKConvex
-- name    : PorteusSS.CaK_iff_quasiKConvex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:53:30.307735+00:00
-- url     : https://prove2.me/theorems/a4c40360-7983-4a36-9bbe-fb64da7a6bc1
-- title:
--   Lemma 9 — $C_a(K)$ functions are exactly the quasi-$K$-convex, piecewise continuous, PF-integrable, coercive functions
-- statement:
--   Let $K \ge 0$ and $f : \mathbb R \to \mathbb R$. If $f \in C_a(K)$ for some $a \in \mathbb R$, then
--
--   1. $f$ is quasi-$K$-convex on $\mathbb R$,
--   2. $f$ is piecewise continuous,
--   3. $f$ is PF-integrable, and
--   4. $f(x) \to \infty$ as $|x| \to \infty$.
--
--   Conversely, if (1)–(4) hold, then $f \in C_a(K)$ for some $a \in \mathbb R$. In short,
--   $$ \bigcup_{a \in \mathbb R} C_a(K) = \{ f : f \text{ quasi-}K\text{-convex, piecewise continuous, PF-integrable}, \ f(x) \to \infty \text{ as } |x| \to \infty \}. $$
--
--   This characterization identifies Porteus's classes with quasi-$K$-convexity, a common extension of Scarf's $K$-convexity and ordinary quasi-convexity; it is the tool used to derive the $(s,S)$ shape of $C(K)$ functions.
--
--   **Formalization Note.** The paper defines $C_a(K)$ only for $K \ge 0$, hence the hypothesis $K \ge 0$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 424, Lemma 9

import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 9 (p. 424). For `K ≥ 0`: if `f ∈ C_a(K)` for some `a`, then `f` is quasi-`K`-convex
on `ℝ`, piecewise continuous, PF-integrable and `f x → ∞` as `|x| → ∞`; conversely these four
properties imply `f ∈ C_a(K)` for some `a ∈ ℝ`. -/
theorem CaK_iff_quasiKConvex (K : ℝ) (hK : 0 ≤ K) (f : ℝ → ℝ) :
    (∀ a : ℝ, CaK a K f →
      QuasiKConvexOn f K univ ∧ PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧
        Tendsto f (cocompact ℝ) atTop) ∧
    (QuasiKConvexOn f K univ ∧ PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧
        Tendsto f (cocompact ℝ) atTop → ∃ a : ℝ, CaK a K f) := by sorry

end PorteusSS
