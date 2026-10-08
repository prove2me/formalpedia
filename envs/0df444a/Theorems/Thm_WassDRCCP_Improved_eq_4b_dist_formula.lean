-- Prove2me | Theorems.Thm_WassDRCCP_Improved_eq_4b_dist_formula
-- name    : WassDRCCP.Improved.eq_4b_dist_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:26.564267+00:00
-- url     : https://prove2.me/theorems/fd0f9a93-35fa-43a6-819c-f5309aacee1e
-- title:
--   (4b), p. 646 — distance to the unsafe set of a joint RHS chance constraint: max{0, min_p (b_p^⊤ξ + d_p − a_p^⊤x)/‖b_p‖_*}
-- statement:
--   Let $E$ be a real normed space, $P \ge 1$, and for each $p \in [P]$ let $b_p$ be a nonzero continuous linear functional on $E$ with dual norm $\|b_p\|_*$, $a_p \in \mathbb R^L$ and $d_p \in \mathbb R$. For $x \in \mathbb R^L$ let
--   $$\mathcal S(x) = \{\xi \in E : b_p^\top\xi + d_p - a_p^\top x > 0,\ p \in [P]\}$$
--   be the safety set of a joint chance constraint with right-hand side uncertainty. Then for every $\xi \in E$ the distance from $\xi$ to the unsafe set $E \setminus \mathcal S(x)$ is
--   $$\operatorname{dist}(\xi, \mathcal S(x)) = \max\Big\{0,\ \min_{p \in [P]} \frac{b_p^\top\xi + d_p - a_p^\top x}{\|b_p\|_*}\Big\}.$$
--
--   This closed form is what turns the distance constraints of the Wasserstein reformulation (3) into the linear big-M constraints of (5) and all later formulations.
--
--   **Formalization Note** $b_p$ is an element of the strong dual of $E$, and $\|b_p\|_*$ is its operator norm, which is exactly the dual norm of $\|\cdot\|$. The distance is `Metric.infDist ξ (S x)ᶜ`. The hypotheses $P \ge 1$ and $b_p \ne 0$ are implicit in the paper (the minimum over $[P]$ and the division by $\|b_p\|_*$ need them); they also make the unsafe set nonempty. The statement holds in any real normed space, so finite dimension is not assumed.
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 646, (4a)–(4b)

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), (4b), p. 646: for the safety set (4a),
`dist(ξ, S(x)) = max {0, min_{p ∈ [P]} (b_p^⊤ξ + d_p − a_p^⊤x)/‖b_p‖_*}`, with `‖b_p‖_*` the
dual norm (the operator norm of the functional `b p`). -/
theorem eq_4b_dist_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (hP : 0 < P) (hb : ∀ p, b p ≠ 0) (x : Fin L → ℝ) (u : E) :
    distUnsafe (safetySet a b d x) u =
      max 0 ((Finset.univ : Finset (Fin P)).inf' ⟨⟨0, hP⟩, Finset.mem_univ _⟩
        (fun p => (b p u + d p - a p ⬝ᵥ x) / ‖b p‖)) := by sorry

end WassDRCCP.Improved
