-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_A_3
-- name    : PackingLPAccel.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:14.756744+00:00
-- url     : https://prove2.me/theorems/3841817b-34da-487d-85a4-40fb8412f298
-- title:
--   Lemma A.3 — an approximate minimizer implements the best response conditions, cited from [CGS25]
-- statement:
--   Let $U\subseteq\mathbb R^n$ be convex, $\psi$ convex on $U$, $v\in\Delta^m$ fixed, $r=r(\cdot,v)$ twice differentiable near $U$, $g\in\mathbb R^n$, $u^\star\in U$ a minimizer of $\langle g,u\rangle+r(u)+\psi(u)$ over $U$, and $\hat u\in U$ with
--
--   $$\langle g,\hat u\rangle+r(\hat u)+\psi(\hat u)\le\langle g,u^\star\rangle+r(u^\star)+\psi(u^\star)+\delta.$$
--
--   If $\lambda_{\min}I\preceq\nabla^2_{u,u}r(u,v)\preceq\lambda_{\max}I$ and the mixed Hessian has largest row sum at most $\beta$ on $U$, with $\lambda_{\max}\ge\lambda_{\min}>0$ and $\beta\ge0$, then the second inequality below holds, and the first holds for all $u\in U$ when $U$ is bounded
--
--   $$\langle g+\nabla_ur(\hat u,v),\hat u-u\rangle+\psi(\hat u)-\psi(u)\le\delta+2\lambda_{\max}\sqrt{\frac{2n\delta}{\lambda_{\min}}}\,\mathrm{Diam}(U),\qquad\|\nabla_vr(u^\star,v)-\nabla_vr(\hat u,v)\|_\infty\le\frac{\beta\sqrt{2\delta}}{\sqrt{\lambda_{\min}}}.$$
--
--   This lemma converts additive accuracy on the regularized subproblem into the two conditions of Definition 5.3.
--
--   Differences from the source:
--   - reading: ∥∇²_{v,u}r(u,v)∥_∞ ≤ β → the ∞→∞ operator norm, the largest row sum; reason: with the entrywise norm of p.7 conclusion 2 is false by a factor √n (r = ½∥u∥² + v₁∑u_j); the proof of Lemma A.2 uses row sums
--   - reading: λ_min I ⪯ ∇²_{u,u}r ⪯ λ_max I → the quadratic form bounds, with the Hessian symmetric on U; reason: the Loewner order is defined on symmetric matrices
--   - encoding: r : U × V → ℝ with its derivatives → r(·,v) with gradient and Hessian on an open neighbourhood W of U; reason: gives the derivatives their meaning at boundary points of U
--   - encoding: Diam(U) is a maximum (p.7) → conclusion 1 for bounded U, conclusion 2 for every convex U; û ∈ U hypothesized; reason: euclDiam is a sup, 0 on unbounded sets, where the printed Diam is undefined; conclusion 2 does not involve Diam; the printed statement uses û in the definition of the feasible point
--   - generalization: r convex; ∇_v r is the gradient of r in v → convexity is not assumed separately; gV is any function with derivative Mix on W; reason: convexity on U follows from the Hessian bound, and ∇_v r is such a function, including for v on the boundary of the simplex
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma A.3, p.33 (pdf 34), cited there as Lemma 5.8 in [CGS25]

import Mathlib
import Definitions.Def_PackingLPAccel_BoxSimplex

namespace PackingLPAccel

/-- **Lemma A.3** (manuscript sha256 1dac7711…, p.33), cited there as Lemma 5.8 in [CGS25].

**Formalization Note.** `v` is fixed, and `r` is the function `r(·, v)`, on an open neighbourhood `W` of `U` so that its
gradient and Hessian have their usual meaning. `gU`, `H`, `gV`, `Mix` are `∇_u r`, `∇²_{u,u} r`, `∇_v r`, `∇²_{v,u} r`.
The norm of the mixed Hessian is the `∞ → ∞` operator norm (largest row sum): with the entrywise `∥·∥_∞` of p.7
conclusion 2 is false by `√n`, and the proof of Lemma A.2 uses row sums. Conclusion 1 is stated for bounded `U`, since
`Diam(U)` is a max (p.7) and `euclDiam` is `0` on an unbounded set; conclusion 2 does not mention `Diam` and holds for
every convex `U`. `gV` need not be tied to `r`, which covers `v` on the boundary of the simplex. -/
theorem lemma_A_3 {n m : ℕ} (U W : Set (Fin n → ℝ)) (_ : Convex ℝ U)
    (_ : IsOpen W) (_ : U ⊆ W)
    (ψ : (Fin n → ℝ) → ℝ) (_ : ConvexOn ℝ U ψ)
    (r : (Fin n → ℝ) → ℝ) (gU : (Fin n → ℝ) → Fin n → ℝ)
    (H : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (gV : (Fin n → ℝ) → Fin m → ℝ) (Mix : (Fin n → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (_ : ∀ u ∈ W, HasFDerivAt r (∑ j, gU u j • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) j) u)
    (_ : ∀ u ∈ W, HasFDerivAt gU (Matrix.mulVecLin (H u)).toContinuousLinearMap u)
    (_ : ∀ u ∈ W, HasFDerivAt gV (Matrix.mulVecLin (Mix u)).toContinuousLinearMap u)
    (g : Fin n → ℝ) (ustar uhat : Fin n → ℝ) (δ : ℝ) (_ : ustar ∈ U) (_ : uhat ∈ U)
    (_ : ∀ u ∈ U, ∑ j, g j * ustar j + r ustar + ψ ustar ≤ ∑ j, g j * u j + r u + ψ u)
    (_ : ∑ j, g j * uhat j + r uhat + ψ uhat ≤ ∑ j, g j * ustar j + r ustar + ψ ustar + δ)
    (lmin lmax β : ℝ) (_ : 0 < lmin) (_ : lmin ≤ lmax) (_ : 0 ≤ β)
    (_ : ∀ u ∈ U, (H u).IsSymm)
    (_ : ∀ u ∈ U, ∀ w : Fin n → ℝ,
      lmin * ∑ j, w j ^ 2 ≤ ∑ j, w j * (H u).mulVec w j ∧
        ∑ j, w j * (H u).mulVec w j ≤ lmax * ∑ j, w j ^ 2)
    (_ : ∀ u ∈ U, ∀ i, ∑ j, |Mix u i j| ≤ β) :
    (Bornology.IsBounded U → ∀ u ∈ U, ∑ j, (g j + gU uhat j) * (uhat j - u j) + ψ uhat - ψ u ≤
      δ + 2 * lmax * Real.sqrt (2 * n * δ / lmin) * euclDiam U) ∧
    ‖fun i => gV ustar i - gV uhat i‖ ≤ β * Real.sqrt (2 * δ) / Real.sqrt lmin := by sorry

end PackingLPAccel
