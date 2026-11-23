-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_Supplement_lemma_5_3
-- name    : ProjSelfConcordant.ConicExt.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:22:47.598523+00:00
-- url     : https://prove2.me/theorems/948a98b7-404c-4595-921f-f209f21bd39b
-- title:
--   Lemma 5.3, p. 13 — the critical point of q_p is unique, a global minimizer with q_p″ ≻ 0, and f′(x∗) = −p/(1 + ⟨x∗, p⟩)
-- statement:
--   Let $X\subset\mathbb R^n$ be a regular convex set with interior $X^o$ and $f$ a projectively self-concordant function on $X$ with some parameter $\gamma\ge0$ ($C^3$ on $X^o$ and satisfying conditions (1) and (3) of Definition 1.4 there; no boundary behaviour is assumed). Let $p$ be a point of the domain of definition of the dual function $f_*$: $1+\langle x,p\rangle>0$ for all $x\in X^o$ and $q_p(x)=f(x)+\log(1+\langle x,p\rangle)$ has a critical point in $X^o$. Let $x^*\in X^o$ be a critical point of $q_p$. Then
--
--   1. $x^*$ is the unique critical point of $q_p$ in $X^o$;
--   2. $x^*$ is a global minimizer of $q_p$ on $X^o$;
--   3. the Hessian $q_p''(x^*)$ is positive definite;
--   4. at $x=x^*$,
--   $$f'(x)=-\frac{p}{1+\langle x,p\rangle},\qquad p=-\frac{f'(x)}{1+\langle f'(x),x\rangle},\qquad 1+\langle f'(x),x\rangle=\frac1{1+\langle x,p\rangle}>0.$$
--
--   The lemma makes $f_*(p)=-\min q_p$ well defined and identifies the minimizer through the duality map.
--
--   **Formalization Note** $f'(x)$ is the gradient vector `gradient f x`; a critical point is a point where the Fréchet derivative of $q_p$ vanishes; the Hessian is the second Fréchet derivative evaluated on $(h,h)$.
--
--   Differences from the source:
--   - encoding: f : Xᵒ → ℝ → a total function on ℝⁿ that is C³ on Xᵒ; reason: only values on the open set Xᵒ enter the statement
--   - encoding: functions and derivatives on open subsets of ℝⁿ → total functions on EuclideanSpace ℝ (Fin n), with Fréchet derivatives evaluated on the stated open domains; reason: every source function extends outside its domain; derivatives at interior points depend only on local values, and the Euclidean inner product identifies covectors with gradients when needed
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 13, Lemma 5.3 (with Definition 5.2)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Duality

namespace ProjSelfConcordant.ConicExt.Supplement

/-- Lemma 5.3, p. 13: let `f` be a projectively self-concordant function on a regular convex set
`X`, let `f∗` be defined at `p`, and let `x∗ ∈ Xᵒ` be a critical point of
`q_p(x) = f(x) + log(1 + ⟨x, p⟩)`. Then `x∗` is the unique critical point of `q_p` in `Xᵒ`, a global
minimizer of `q_p` on `Xᵒ`, `q_p″(x∗) ≻ 0`, and at `x = x∗`:
`f′(x) = −p/(1 + ⟨x, p⟩)`, `p = −f′(x)/(1 + ⟨f′(x), x⟩)`, `1 + ⟨f′(x), x⟩ = 1/(1 + ⟨x, p⟩) > 0`. -/
theorem lemma_5_3 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (γ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ProjSCFun γ X f) (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ dualDomain X f)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ interior X)
    (hcrit : fderiv ℝ (qfun f p) xs = 0) :
    (∀ y ∈ interior X, fderiv ℝ (qfun f p) y = 0 → y = xs) ∧
    (∀ y ∈ interior X, qfun f p xs ≤ qfun f p y) ∧
    (∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 → 0 < d2 (qfun f p) xs h h) ∧
    gradient f xs = -(1 + inner ℝ xs p)⁻¹ • p ∧
    p = -(1 + inner ℝ (gradient f xs) xs)⁻¹ • gradient f xs ∧
    1 + inner ℝ (gradient f xs) xs = (1 + inner ℝ xs p)⁻¹ ∧
    0 < (1 + inner ℝ xs p)⁻¹ := by sorry

end ProjSelfConcordant.ConicExt.Supplement
