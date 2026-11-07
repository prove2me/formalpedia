-- Prove2me | Theorems.Thm_SubsetConvFPRAS_theorem_3_2
-- name    : SubsetConvFPRAS.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:44.941279+00:00
-- url     : https://prove2.me/theorems/a9a30e46-2723-47f2-803b-0a34e1a4b56f
-- title:
--   Theorem 3.2 — stochastic coordinate descent finds a point with $\|\nabla f\|_\infty\le\eta$ in $O(Q)$ oracle calls
-- statement:
--   Fix $d\ge1$, $x_0\in\mathbb R^d$, $L,\sigma>0$ and $H_0\ge0$. Let $f:\mathbb R^d\to\mathbb R$ be convex and differentiable with
--   $$f(x+ue_i)\le f(x)+u\,\partial_if(x)+Lu^2/2\quad(13),\qquad f(x)\ge f(x_0)-H_0\quad(14)$$
--   for all $x$, $u$ and $i$. Let the gradient oracle $G(x)$ use fresh independent randomness, cost at most $T\ge d$ per query, be unbiased, $\mathbb E[G(x)]=\nabla f(x)$, and have coordinatewise $\sigma$-sub-Gaussian noise, $\mathbb E\exp(u(G_i(x)-\partial_if(x)))\le\exp(\sigma^2u^2/2)$. Then for $0<\eta\le1$ and $0<\delta<1$ the stochastic coordinate-descent algorithm of Appendix A.4 (any step $s\in[\eta/(16L),\eta/(8L)]$, any rule choosing a coordinate with $|\hat g_i|>\eta/2$) satisfies, with one universal constant $C$:
--
--   1. with probability at least $1-\delta$ it returns $x$ with $\|\nabla f(x)\|_\infty\le\eta$;
--   2. on every execution every queried or returned point $y$ has $\|y-x_0\|_1\le C(H_0/\eta+\eta/L)$, (15);
--   3. on every execution it uses at most $CQ$ oracle calls and total time at most $CTQ$, where
--   $$Q=\Bigl(1+\frac{\sigma^2}{\eta^2}\Bigr)\Bigl(1+\frac{LH_0}{\eta^2}\Bigr)\log\Bigl(\frac{2d}{\delta}\Bigl(1+\frac{LH_0}{\eta^2}\Bigr)\Bigr).\tag{16}$$
--
--   Corollary 5.12 applies this to $\Phi$ with $L=\sigma=1$, $H_0=B$, gradient samples supplied by Corollary 5.6.
--
--   Differences from the source:
--   - generalization: "a stochastic coordinate-descent algorithm" has the guarantees → the algorithm of Appendix A.4 has them, for every admissible step s and every selection rule; reason: a specific algorithm with the guarantees implies the existence the page asserts
--   - reading: fresh independent randomness → the j-th query reads the j-th coordinate of an i.i.d. tape under the product of a probability measure P, with G jointly measurable and the selection rule measurable; reason: the standard model of independent oracle randomness
--   - encoding: E[G(x)] = ∇f(x) and E exp(u(G_i − ∂_i f)) ≤ exp(σ²u²/2) → these with the integrability of G_i(x) and of the exponential stated as hypotheses; reason: the page's expectations presuppose them; without them Lean's integral is 0 and the hypotheses would be vacuous
--   - encoding: O(·) → one universal constant C, chosen before all parameters; reason: standard reading of the O-notation
--   - encoding: total time of an execution → cdTime: T per oracle call plus d·m̂ per batch for averaging and selecting a coordinate; reason: the cost accounting of p.38 (each query costs at most T, averaging and selecting cost O(d m̂) per batch)
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem 3.2, p.18 (algorithm and proof pp.38–39)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_CoordinateDescent

open scoped Classical

namespace SubsetConvFPRAS

open MeasureTheory in
/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Theorem 3.2, p.18; the algorithm is on p.38. For `f` convex,
differentiable, coordinatewise `L`-smooth (13), with gap at most `H₀` (14), and an unbiased coordinatewise
`σ`-sub-Gaussian gradient oracle of cost at most `T ≥ d`, the stochastic coordinate-descent algorithm satisfies:
(a) with probability at least `1 - δ` it returns `x` with `‖∇f(x)‖∞ ≤ η`, and on every execution every queried or
returned `y` has `‖y - x₀‖₁ = O(H₀/η + η/L)`, (15); (b) on every execution it uses `O(Q)` oracle calls and total
time `O(TQ)`, with `Q` from (16).

**Formalization Note.** `C` is universal: it is chosen before every parameter. The step `s` is any value in
`[η/(16L), η/(8L)]`, (25), and `sel` is any measurable rule choosing a coordinate with `|ĝ_i| > η/2` when one exists.
The oracle is jointly measurable with integrable coordinates and exponential moments. The failure event is bounded
as a set under the product measure of the tape. -/
theorem theorem_3_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (x₀ : Fin d → ℝ) (L σ H₀ : ℝ), 0 < L → 0 < σ → 0 ≤ H₀ →
      ∀ (f : (Fin d → ℝ) → ℝ), ConvexOn ℝ Set.univ f → Differentiable ℝ f →
        (∀ (x : Fin d → ℝ) (u : ℝ) (i : Fin d),
          f (x + u • Pi.single i 1) ≤ f x + u * partialAt f x i + L * u ^ 2 / 2) →
        (∀ x, f x₀ - H₀ ≤ f x) →
      ∀ (T : ℝ), (d : ℝ) ≤ T →
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
        (G : (Fin d → ℝ) → Ξ → (Fin d → ℝ)),
        Measurable (Function.uncurry G) →
        (∀ x i, Integrable (fun ξ => G x ξ i) P) →
        (∀ x i, ∫ ξ, G x ξ i ∂P = partialAt f x i) →
        (∀ x i (u : ℝ), Integrable (fun ξ => Real.exp (u * (G x ξ i - partialAt f x i))) P) →
        (∀ x i (u : ℝ),
          ∫ ξ, Real.exp (u * (G x ξ i - partialAt f x i)) ∂P ≤ Real.exp (σ ^ 2 * u ^ 2 / 2)) →
      ∀ (η δ s : ℝ), 0 < η → η ≤ 1 → 0 < δ → δ < 1 → η / (16 * L) ≤ s → s ≤ η / (8 * L) →
      ∀ (sel : (Fin d → ℝ) → Fin d), Measurable sel →
        (∀ g : Fin d → ℝ, (∃ i, η / 2 < |g i|) → η / 2 < |g (sel g)|) →
        let tr : (ℕ → Ξ) → CDTrace d := fun ω => cdRun G x₀ L σ H₀ η δ s sel ω
        let m : ℕ := cdBatch σ η d (cdK L H₀ η) δ
        Measure.infinitePi (fun _ : ℕ => P)
            {ω | ¬ ∃ x, (tr ω).out = some x ∧ ∀ i, |partialAt f x i| ≤ η} ≤ ENNReal.ofReal δ ∧
        (∀ ω, (∀ y ∈ (tr ω).queried, ∑ i, |y i - x₀ i| ≤ C * (H₀ / η + η / L)) ∧
            (∀ y, (tr ω).out = some y → ∑ i, |y i - x₀ i| ≤ C * (H₀ / η + η / L))) ∧
        ∀ ω, ((tr ω).calls : ℝ) ≤ C * cdQ L σ H₀ η δ d ∧
            cdTime T d m (tr ω) ≤ C * (T * cdQ L σ H₀ η δ d) := by sorry

end SubsetConvFPRAS
