-- Prove2me | Theorems.Thm_WeylPolyhedra_Pyramid_reduction_step
-- name    : WeylPolyhedra.Pyramid.reduction_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:15:59.867979+00:00
-- url     : https://prove2.me/theorems/3a91b71e-1010-43d9-8595-6ee17b8c40e1
-- title:
--   §2 a), p. 292 — shifting a point along a generator onto an extreme support plane
-- statement:
--   Let $S \subset \mathbb{R}^n$ be a finite non-degenerate point system, let $\beta$ be an extreme support of $S$, and let $p$ be a point that satisfies every extreme support inequality of $S$: $\langle \alpha, p\rangle \ge 0$ for every extreme support $\alpha$. Then there are a point $e \in S$ with $\langle \beta, e\rangle > 0$ and a number $\lambda \ge 0$ such that the point $q = p - \lambda e$ satisfies
--
--   $$\langle \alpha, q\rangle \ge 0 \ \text{ for every extreme support } \alpha, \qquad \langle \alpha_*, q\rangle = 0 \ \text{ for some extreme support } \alpha_* \text{ with } \langle \alpha_*, e\rangle > 0 .$$
--
--   In Weyl's construction, $e$ is a point of $S$ not on the plane $\langle\beta,x\rangle = 0$, the extreme supports split into a first class ($\langle\alpha,e\rangle>0$, nonempty since it contains $\beta$) and a second class ($\langle\alpha,e\rangle=0$), and $\lambda$ is the minimum of $\langle\alpha,p\rangle/\langle\alpha,e\rangle$ over the first class.
--
--   This step reduces the representation of $p$ to that of $q$, which lies on an extreme support plane: $p = q + \lambda e$ with $\lambda \ge 0$ and $e \in S$. Choosing $e$ in $S$ (rather than the "centre" $a + b + \cdots$) is what makes the count of Satz 2 work.
--
--   **Formalization Note** The number $\lambda$ is named `l` in Lean. The conclusion records the properties of $q$ that the proof uses, not the particular minimising formula.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 292, §2 a) ("Für spätere Zwecke ... wenigstens einer Stützgleichung: (αq) = 0")

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §2 a), p. 292 (the modified first step of case a)): let `S ⊆ ℝⁿ` be finite and
non-degenerate, `β` an extreme support of `S`, and `p` a point satisfying every extreme support
inequality of `S`. Then there is a point `e ∈ S` with `β ⬝ᵥ e > 0` and a number `l ≥ 0` (Weyl's
`λ`) such that `q = p - l • e` still satisfies every extreme support inequality `α ⬝ᵥ q ≥ 0`,
and lies on the plane `α ⬝ᵥ q = 0` of at least one extreme support `α` with `α ⬝ᵥ e > 0` (an
extreme support of "the first class"). -/
theorem reduction_step {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (β : Fin n → ℝ) (hβ : Shared.IsExtremeSupport S β) (p : Fin n → ℝ)
    (hp : ∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ p) :
    ∃ e ∈ S, 0 < β ⬝ᵥ e ∧ ∃ l : ℝ, 0 ≤ l ∧
      (∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ (p - l • e)) ∧
      ∃ α : Fin n → ℝ, Shared.IsExtremeSupport S α ∧ 0 < α ⬝ᵥ e ∧ α ⬝ᵥ (p - l • e) = 0 := by sorry

end WeylPolyhedra.Pyramid
