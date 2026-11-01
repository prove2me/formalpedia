-- Prove2me | Theorems.Thm_SConvexGS_proof_thm3_gradient_exchange
-- name    : SConvexGS.proof_thm3_gradient_exchange
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:08.957055+00:00
-- url     : https://prove2.me/theorems/eab881d1-c001-4e5a-9b56-99efce575013
-- title:
--   Proof of Theorem 3, pp.15–16 — the gradient exchange claim $p_i-q_i>\beta(p_j-q_j)$
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$ be a lower semicontinuous, continuously differentiable, strictly convex function with an open $\operatorname{dom}(f)$, and let $f^*$ be submodular. Let $x,y\in\operatorname{dom}(f)$, $p=\nabla f(x)$, $q=\nabla f(y)$ and $i\in\operatorname{supp}^+(x-y)$. Then there exist $j\in\operatorname{supp}^-(x-y)\cup\{0\}$ and $\beta>0$ such that
--
--   $$p_i-q_i>\beta(p_j-q_j),$$
--
--   where $p_0-q_0=0$. This is the first-order form of the exchange property: it says that $f(x)+f(y)$ strictly decreases to first order along $\mathbf e_i-\beta\mathbf e_j$.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → (−∞, ∞] → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊥; reason: Lean convention; same functions, with ⊤ for +∞
--   - encoding: continuously differentiable, strictly convex or concave f → ContDiffOn and StrictConvexOn or StrictConcaveOn of toReal ∘ f on dom f; reason: these notions apply to the finite part of f, on the open set dom f; toReal of ±∞ is 0, so the set cannot be univ
--   - encoding: p = ∇f(x) → ∀ v, fderiv ℝ (toReal ∘ f) x v = p ⬝ᵥ v; reason: the gradient is the vector representing the derivative under the dot product
--   - encoding: pⱼ − qⱼ for j ∈ {0} ∪ [n] → (p − q) ⬝ᵥ basisOrZero j; reason: equal for j ∈ [n], and 0 at j = 0, the paper's convention in its case (a)
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Proof of Theorem 3, pp.15–16

import Mathlib
import Definitions.Def_SConvexGS_dom
import Definitions.Def_SConvexGS_basisOrZero
import Definitions.Def_SConvexGS_convexConj
import Definitions.Def_SConvexGS_IsSubmodular

open Matrix

namespace SConvexGS

/-- Proof of Theorem 3, pp.15–16 (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29)):
under the hypotheses of Theorem 3, let `x, y ∈ dom(f)`, `p = ∇f(x)`, `q = ∇f(y)` and
`i ∈ supp⁺(x − y)`. Then there exist `j ∈ supp⁻(x − y) ∪ {0}` and `β > 0` such that
`pᵢ − qᵢ > β(pⱼ − qⱼ)`.

Formalization Note: `pⱼ − qⱼ` is `(p − q) ⬝ᵥ basisOrZero j`, which is `0` at `j = none`, the paper's
convention `p₀ − q₀ = 0` in case (a). -/
theorem proof_thm3_gradient_exchange {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_bot : ∀ x, f x ≠ ⊥) (hf_lsc : LowerSemicontinuous f) (hf_open : IsOpen (dom f))
    (hf_C1 : ContDiffOn ℝ 1 (fun x => (f x).toReal) (dom f))
    (hf_strict : StrictConvexOn ℝ (dom f) (fun x => (f x).toReal))
    (hf_sub : IsSubmodular (convexConj f))
    (x y : Fin n → ℝ) (hx : x ∈ dom f) (hy : y ∈ dom f) (p q : Fin n → ℝ)
    (hp : ∀ v, fderiv ℝ (fun x => (f x).toReal) x v = p ⬝ᵥ v)
    (hq : ∀ v, fderiv ℝ (fun x => (f x).toReal) y v = q ⬝ᵥ v)
    (i : Fin n) (hi : y i < x i) :
    ∃ j : Option (Fin n), (j = none ∨ ∃ j' : Fin n, j = some j' ∧ x j' < y j') ∧
      ∃ β : ℝ, 0 < β ∧ p i - q i > β * ((p - q) ⬝ᵥ basisOrZero j) := by sorry

end SConvexGS
