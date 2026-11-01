-- Prove2me | Theorems.Thm_SConvexGS_proof_thm3_legendre_duality
-- name    : SConvexGS.proof_thm3_legendre_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:09.482989+00:00
-- url     : https://prove2.me/theorems/56959fc2-a305-4088-a4c0-b3d58ce29cce
-- title:
--   Proof of Theorem 3, p.15 — $x=\nabla f^*(p)$ and $\{p\}=\arg\min f^*[-x]$ for $p=\nabla f(x)$
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$ be a lower semicontinuous, continuously differentiable, strictly convex function with an open $\operatorname{dom}(f)$. Let $x\in\operatorname{dom}(f)$ and $p=\nabla f(x)$. Then:
--
--   1. $p\in\operatorname{int}(\operatorname{dom}f^*)$;
--   2. $f^*$ is differentiable at $p$ with $\nabla f^*(p)=x$;
--   3. $p$ is the unique minimizer of $f^*[-x]$, that is, $f^*(p)-x^{T}p<f^*(r)-x^{T}r$ for every $r\ne p$.
--
--   This is Legendre duality for $f$, which the proof of Theorem 3 uses to compare gradients of $f$ through values of $f^*$.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → (−∞, ∞] → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊥; reason: Lean convention; same functions, with ⊤ for +∞
--   - encoding: continuously differentiable, strictly convex or concave f → ContDiffOn and StrictConvexOn or StrictConcaveOn of toReal ∘ f on dom f; reason: these notions apply to the finite part of f, on the open set dom f; toReal of ±∞ is 0, so the set cannot be univ
--   - encoding: p = ∇f(x) → ∀ v, fderiv ℝ (toReal ∘ f) x v = p ⬝ᵥ v; reason: the gradient is the vector representing the derivative under the dot product
--   - encoding: the pair (x, p), (y, q) → one point (x, p); reason: the statement for y is the same statement
--   - encoding: x = ∇f*(p) → p ∈ interior (dom f*), DifferentiableAt of toReal ∘ f* at p, and ∀ v, fderiv … p v = x ⬝ᵥ v; reason: this is what the gradient of the extended-valued f* at p means
--   - encoding: {p} = arg min f*[−x] → f*(p) − xᵀp < f*(r) − xᵀr for every r ≠ p; reason: the definition of a unique minimizer
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Proof of Theorem 3, p.15

import Mathlib
import Definitions.Def_SConvexGS_dom
import Definitions.Def_SConvexGS_convexConj

open Matrix

namespace SConvexGS

/-- Proof of Theorem 3, p.15 (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29)):
let `f : ℝⁿ → (−∞, ∞]` be lsc, continuously differentiable and strictly convex with an open
`dom(f)`, `x ∈ dom(f)` and `p = ∇f(x)`. Then `p ∈ int(dom f*)`, `x = ∇f*(p)` and
`{p} = arg min f*[−x]`.

Formalization Note: `p` represents `∇f(x)` through `∀ v, fderiv ℝ F x v = p ⬝ᵥ v`, and likewise `x`
represents `∇f*(p)`, the derivative at `p` of `toReal ∘ f*`. The membership in the interior is what
"`x = ∇f*(p)`" needs. `{p} = arg min f*[−x]` is the strict inequality for every `r ≠ p`. The paper
prints the pair `(x, p)`, `(y, q)`; one point is stated. -/
theorem proof_thm3_legendre_duality {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_bot : ∀ x, f x ≠ ⊥) (hf_lsc : LowerSemicontinuous f) (hf_open : IsOpen (dom f))
    (hf_C1 : ContDiffOn ℝ 1 (fun x => (f x).toReal) (dom f))
    (hf_strict : StrictConvexOn ℝ (dom f) (fun x => (f x).toReal))
    (x : Fin n → ℝ) (hx : x ∈ dom f) (p : Fin n → ℝ)
    (hp : ∀ v, fderiv ℝ (fun x => (f x).toReal) x v = p ⬝ᵥ v) :
    p ∈ interior (dom (convexConj f)) ∧
    DifferentiableAt ℝ (fun r => (convexConj f r).toReal) p ∧
    (∀ v, fderiv ℝ (fun r => (convexConj f r).toReal) p v = x ⬝ᵥ v) ∧
    ∀ r, r ≠ p →
      convexConj f p - ((x ⬝ᵥ p : ℝ) : EReal) < convexConj f r - ((x ⬝ᵥ r : ℝ) : EReal) := by sorry

end SConvexGS
