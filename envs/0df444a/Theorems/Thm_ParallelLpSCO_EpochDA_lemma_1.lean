-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_lemma_1
-- name    : ParallelLpSCO.EpochDA.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:04:33.551092+00:00
-- url     : https://prove2.me/theorems/0066957a-dfa8-40d9-a1da-d459b2a5adfe
-- title:
--   Lemma 1 — p-GREG is unbiased for $\nabla\hat f_{\rho,p}$, and its $q$-th moment is at most $3G^q$ on $B_p(\bar x,\rho)$
-- statement:
--   Let $p\ge2$, $q=p/(p-1)$, $f:\mathbb R^d\to\mathbb R$ convex, and $g$ a gradient estimator with $\mathbb E[g(z)]\in\partial f(z)$ for every $z$. Fix $\rho>0$, an anchor $\bar x$ and a point $x$. With $\xi\sim GG_p(0,\rho^2)$ sampled first and $g$ queried independently at $\bar x+\xi$, the p-GREG estimator is
--   $$\tilde\nabla^g_{\bar x}\hat f_{\rho,p}(x)=\frac{\gamma_{\rho,p}(x-\bar x-\xi)}{\gamma_{\rho,p}(\xi)}\,g(\bar x+\xi).$$
--   Lemma 1 states:
--   1. $\mathbb E[\tilde\nabla^g_{\bar x}\hat f_{\rho,p}(x)]=\nabla\hat f_{\rho,p}(x)$;
--   2. if $\mathbb E\|g(z)\|_q^q\le G^q$ for all $z$ and $x\in B_p(\bar x,\rho)$, then
--   $$\mathbb E\|\tilde\nabla^g_{\bar x}\hat f_{\rho,p}(x)\|_q^q\le 3G^q.$$
--
--   This is the estimator behind every parallel algorithm of the paper. All its queries are at points $\bar x+\xi$ that do not depend on $x$, so a whole batch of estimates at future iterates can be queried in one round.
--
--   **Formalization Note.** The first clause asserts that the estimator is integrable under $GG_p(0,\rho^2)\otimes\mathrm{Unif}[0,1]$ and that $\hat f_{\rho,p}$ (`fHat`) is Fréchet differentiable at $x$ with derivative $h\mapsto\langle\mathbb E[\tilde\nabla],h\rangle$.
--
--   Differences from the source:
--   - encoding: a gradient estimator g with E[g] ∈ ∂f (Definition 2) → a jointly measurable map g(z, u) of the query point and one uniform draw u ∈ [0, 1], with g(z, ·) integrable and its Bochner mean a subgradient of f at z, for every z; reason: every Markov kernel into ℝ^d is the law of such a map; the source's E[g] presupposes the mean exists, and Lean's integral of a non-integrable function is 0
--   - encoding: E[∇̃] = ∇f̂_{ρ,p}(x) → the estimator is integrable and f̂_{ρ,p} has Fréchet derivative h ↦ ⟨E[∇̃], h⟩ at x; reason: the source asserts the expectation and the gradient exist
--   - encoding: E‖g(z)‖_q^q ≤ G^q → 0 ≤ G and qMoment p g z ≤ G^q; reason: G^q is undefined for G < 0
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 7, Lemma 1

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Lemma 1 (p. 7). For the p-GREG estimator of radius `ρ` anchored at `x̄`, with
`ξ ∼ GG_p(0, ρ²)` and an independent oracle draw `u`, for an estimator `g` whose mean
`E[g(z)]` exists and is a subgradient of `f` at every `z`: (i) it is integrable and its mean is the
gradient of `f̂_{ρ,p}` at `x`; (ii) if `E‖g(z)‖_q^q ≤ G^q` for all `z` and `x ∈ B_p(x̄, ρ)`, its
`q`-th moment is at most `3G^q`. -/
theorem lemma_1 (p : ℝ) (hp : 2 ≤ p) (d : ℕ) (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (g : Oracle d) (hgm : Measurable (Function.uncurry g)) (hgi : ∀ z, Integrable (g z))
    (hg : ∀ z, IsSubgrad f z (∫ u, g z u))
    (ρ : ℝ) (hρ : 0 < ρ) (xbar x : Vec d) :
    let μ : Measure (Vec d × unitInterval) := (ggLaw d p ρ).prod (volume : Measure unitInterval)
    let est : Vec d × unitInterval → Vec d := fun ξu => pgreg p ρ xbar x ξu.1 (g (xbar + ξu.1) ξu.2)
    (Integrable est μ ∧
      HasFDerivAt (fHat p ρ f)
        (∑ i, (∫ ξu, est ξu ∂μ) i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
        x) ∧
    (∀ G : ℝ, 0 ≤ G → (∀ z, qMoment p g z ≤ ENNReal.ofReal (G ^ conjExp p)) →
      x ∈ lpBall p xbar ρ →
      ∫⁻ ξu, ENNReal.ofReal (lpNorm (conjExp p) (est ξu) ^ conjExp p) ∂μ ≤
        ENNReal.ofReal (3 * G ^ conjExp p)) := by sorry

end ParallelLpSCO.EpochDA
