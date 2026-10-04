-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_osgd_two_point_regret_bound
-- name    : RegretBandits.Nonlinear.osgd_two_point_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:42:44.849979+00:00
-- url     : https://prove2.me/theorems/42e2da94-9134-4ef2-b89e-626fbcd49b5d
-- title:
--   Theorem 6.1 (first display) — pseudo-regret of OSGD with two-point feedback
-- statement:
--   Let $d\ge1$ and let $\mathcal K\subseteq\mathbb R^d$ be closed and convex with $r\,\mathbb B\subseteq\mathcal K\subseteq R\,\mathbb B$ for some $r,R>0$. Let $\ell_1,\ell_2,\dots:\mathbb R^d\to\mathbb R$ be a fixed sequence of $G$-Lipschitz, differentiable and convex losses. Fix $\delta$ with $0<\delta\le r$ and a learning rate $\eta>0$.
--
--   On a probability space let $(S_t,C_t)_{t\ge1}$ be independent pairs, where $S_t$ is uniform on the unit sphere $\mathbb S$ and $C_t$ is an independent fair sign in $\{-1,+1\}$. Run OSGD on $(1-\delta/r)\mathcal K$ with learning rate $\eta$ and the two-point estimates (6.1)
--   $$\widetilde g_t(x_t)=\frac{d}{2\delta}\big(\ell_t(X_t^+)-\ell_t(X_t^-)\big)S_t,\qquad X_t^\pm=x_t\pm\delta S_t,$$
--   and play $\widetilde X_t=x_t+C_t\delta S_t$, which is $X_t^+$ or $X_t^-$ with probability $1/2$ each. Then the pseudo-regret satisfies
--   $$\overline R_n=\mathbb E\sum_{t=1}^n\ell_t(\widetilde X_t)-\min_{x\in\mathcal K}\sum_{t=1}^n\ell_t(x)\le\frac{R^2}{\eta}+\eta(Gd)^2n+\delta\Big(3+\frac Rr\Big)Gn .$$
--
--   This is the $\mathcal O(\sqrt n)$ guarantee of the two-point feedback model.
--
--   **Formalization Note** Added hypothesis $\delta\le r$: the book does not state it, but its proof needs it so that $(1-\delta/r)\mathcal K$ is a shrinking of $\mathcal K$ and $X_t^\pm\in\mathcal K$. "Drawn at random between $X_t^+$ and $X_t^-$" is read as a fair coin independent of everything else, as the proof's step $\mathbb E(\ell_t(\widetilde X_t)\mid X_t^\pm)=\frac12(\ell_t(X_t^+)+\ell_t(X_t^-))$ requires. The losses are oblivious: fixed before the run. They are Lipschitz, differentiable and convex on all of $\mathbb R^d$ (Lemmas 6.1–6.2 take $\ell:\mathbb R^d\to\mathbb R$). The constant $R^2/\eta$ is the book's form.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 93, Theorem 6.1 (first display)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD

open MeasureTheory ProbabilityTheory
open scoped NNReal Pointwise

namespace RegretBandits.Nonlinear

/-- Theorem 6.1, first display (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 93): regret of OSGD
with two-point feedback. Let `d ≥ 1` and let `K ⊆ ℝ^d` be closed and convex with
`r𝔹 ⊆ K ⊆ R𝔹`, `r, R > 0`. Let `ℓ_1, ℓ_2, … : ℝ^d → ℝ` be a fixed sequence of `G`-Lipschitz,
differentiable and convex losses. Fix `0 < δ ≤ r` (the bound `δ ≤ r` is not printed; the proof
needs it) and `η > 0`. On a probability space, let `(S_t, C_t)_{t ≥ 1}` be independent pairs with
`S_t` uniform on the unit sphere and `C_t` an independent fair sign in `{-1, +1}`. Let `x_t` be
the OSGD run on `(1 - δ/r)K` with learning rate `η` and the two-point estimates (6.1)
`g̃_t(x_t) = (d/(2δ)) (ℓ_t(x_t + δS_t) - ℓ_t(x_t - δS_t)) S_t`, and let the played point be
`X̃_t = x_t + C_t δ S_t` (drawn at random between `X⁺_t` and `X⁻_t`). Then
`R̄_n ≤ R²/η + η(Gd)²n + δ(3 + R/r)Gn`. -/
theorem osgd_two_point_regret_bound
    {d : ℕ} (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKclosed : IsClosed K) (hKconv : Convex ℝ K)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hrK : Metric.closedBall 0 r ⊆ K) (hKR : K ⊆ Metric.closedBall 0 R)
    (G : ℝ≥0) (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓlip : ∀ t, LipschitzWith G (ℓ t)) (hℓdiff : ∀ t, Differentiable ℝ (ℓ t))
    (hℓconv : ∀ t, ConvexOn ℝ Set.univ (ℓ t))
    (δ η : ℝ) (hδ : 0 < δ) (hδr : δ ≤ r) (hη : 0 < η)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (C : ℕ → Ω → ℝ)
    (hSm : ∀ t, Measurable (S t)) (hCm : ∀ t, Measurable (C t))
    (hind : iIndepFun (fun t ω => (S t ω, C t ω)) P)
    (hlaw : ∀ t, P.map (fun ω => (S t ω, C t ω)) = (uniformSphere d).prod fairSign)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ ω, IsOSGDRun ((1 - δ / r) • K) η
      (fun t y => twoPointEstimate d δ (ℓ t) (S t ω) y) (fun t => x t ω))
    (n : ℕ) :
    pseudoRegret K ℓ P (fun t ω => x t ω + (C t ω * δ) • S t ω) n ≤
      R ^ 2 / η + η * ((G : ℝ) * d) ^ 2 * n + δ * (3 + R / r) * G * n := by sorry

end RegretBandits.Nonlinear
