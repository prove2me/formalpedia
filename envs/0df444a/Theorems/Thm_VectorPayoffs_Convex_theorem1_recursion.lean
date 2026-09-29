-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_theorem1_recursion
-- name    : VectorPayoffs.Convex.theorem1_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:08:13.346999+00:00
-- url     : https://prove2.me/theorems/b37a82b3-198c-41a9-a027-409f54f19f01
-- title:
--   Proof of THEOREM 1, (5)–(7) — the squared distance of x̄ₙ from S satisfies (5), (6), (7) with c = (diam X)², uniformly in II's strategy
-- statement:
--   Assume the hypotheses of THEOREM 1: $S\subseteq\mathbb R^N$ is closed, $p(\cdot)$ assigns to every $x\notin S$ a mixed action $p(x)\in P$ such that for some point $y\in S$ closest to $x$ the hyperplane through $y$ perpendicular to $xy$ separates $x$ from $R(p(x))$, and $f$ is a strategy of I with $f_n(x_1,\dots,x_n)=p(\bar x_n)$ whenever $n\ge1$ and $\bar x_n\notin S$.
--
--   Then there are constants $a,b$ such that for every strategy $g$ of II and every play $x_1,x_2,\dots$ of $(f,g)$, the squared distances
--   $$\delta_n=\operatorname{dist}(\bar x_n,S)^2$$
--   satisfy (5), (6) and (7) with these $a,b$ and with $c=(\operatorname{diam}X)^2$.
--
--   This is the deterministic-to-probabilistic reduction in the proof of THEOREM 1: combined with the LEMMA it gives approachability.
--
--   **Formalization Note** The constants $a,b,c$ are chosen before II's strategy and the play, as the LEMMA's uniform rate requires. The paper says only that "$c$ depends only on the size of the bounded set $X$"; the statement fixes the value $(\operatorname{diam}X)^2$ that its displays (2)–(4) produce, which is the stronger claim. The hypotheses force $S\ne\emptyset$, so the real-valued distance `Metric.infDist` is used here.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 3 (definition of δ_n in the proof of THEOREM 1) and p. 4, displays (5), (6), (7)

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game
import Definitions.Def_VectorPayoffs_Convex_Recursion

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §2, proof of THEOREM 1, p. 4, (5)–(7): under THEOREM 1's hypotheses, the
squared distances `δₙ = d(x̄ₙ, S)²` satisfy (5), (6), (7) with `c = (diam X)²` and constants
`a, b` chosen before II's strategy. -/
theorem theorem1_recursion {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (hS : IsClosed S)
    (p : E N → Fin r → ℝ)
    (hsep : ∀ x ∉ S, p x ∈ stdSimplex ℝ (Fin r) ∧ G.BlackwellCondition S (p x) x)
    (f : Strategy N r)
    (hf : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∉ S → f.toFun n h = p (avgHist h)) :
    ∃ a b : ℝ, ∀ (g : Strategy N s) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (x : ℕ → Ω → E N), G.IsPlay f g μ x →
        SatisfiesRecursion a b (Metric.diam G.X ^ 2) μ
          (fun n ω => Metric.infDist (avg x n ω) S ^ 2) := by sorry

end VectorPayoffs.Convex
