-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_6_3
-- name    : SKWeakPoincare.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:47.896802+00:00
-- url     : https://prove2.me/theorems/458bbd5b-9e61-409f-9336-4ee393836186
-- title:
--   Lemma 6.3 — posterior comparison via the symmetric KL divergence
-- statement:
--   Let $n\ge2$ and let $\mu$ be a full-support law on $\{\pm1\}^n$, with tilts $\mu_y$ and posterior mean $m$.
--
--   1. For every $y,z\in\mathbb R^n$ and $f:\{\pm1\}^n\to\mathbb R$,
--   $$
--   \big|E_{\mu_y}[f]-E_{\mu_z}[f]\big|^2\le2\Big(\exp\big([D(\mu_y\|\mu_z)+D(\mu_z\|\mu_y)]/2\big)-1\Big)\big(\mathrm{Var}_{\mu_y}[f]+\mathrm{Var}_{\mu_z}[f]\big).
--   $$
--   2. If $T,L>0$ and $\mathfrak e$ is a cost function for which $m$ has the Lipschitz property with cost functions (as in Lemma 6.1), then for every $y,z\in\mathbb R^n$,
--   $$
--   D(\mu_y\|\mu_z)+D(\mu_z\|\mu_y)\le L\|y-z\|_2^2+\Big(\sqrt{\mathfrak e(T;y)}+\sqrt{\mathfrak e(T;z)}\Big)\|y-z\|_2 .
--   $$
--
--   The two parts bound the gap between the posterior expectations at the endpoints of two nearby localization paths (proof of Lemma 6.1).
--
--   **Formalization Note** $\mu_y=$ `tilt μ y`, and $D$ is the finite-sum KL divergence `lawKL`. Fields are Euclidean vectors.
--
--   Differences from the source:
--   - encoding: the posterior distribution μ_y and cost function 𝔢 'defined above' (Lemma 6.1) → 2 ≤ n and IsFullSupportLaw μ; in part 2, 0 < T, 0 < L, IsCostFn T n e and HasLipCost T L (postMean μ) e; reason: the lemma refers to the objects of Lemma 6.1
--   - encoding: y, z ∈ ℝⁿ with the Euclidean norm ‖y − z‖₂ → y z : EuclideanSpace ℝ (Fin n), passed to tilt through WithLp.ofLp; reason: same vectors and norm
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 6.3, p.38 (proof pp.38–39), in the setting of Lemma 6.1, p.37

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKWeakPoincare_postMean
import Definitions.Def_SKWeakPoincare_IsCostFn

open OAI.CriticalSK SKAnnealing.Sampling

namespace SKWeakPoincare

/-- **Lemma 6.3 (posterior comparison via the symmetric KL divergence).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 6.3, p. 38 (proof pp. 38–39), in the setting of Lemma 6.1, p. 37.

Let `n ≥ 2` and `μ` a full-support distribution on `{±1}^n`, with tilts `μ_y` and posterior mean `m`.
(a) For every `y, z ∈ ℝ^n` and `f : {±1}^n → ℝ`,
`|E_{μ_y}[f] − E_{μ_z}[f]|² ≤ 2(exp([D(μ_y‖μ_z) + D(μ_z‖μ_y)]/2) − 1)(Var_{μ_y}[f] + Var_{μ_z}[f])`.
(b) If `T, L > 0` and `𝔢` is a cost function with the Lipschitz property with cost functions for `m`
(as in Lemma 6.1), then for every `y, z ∈ ℝ^n`,
`D(μ_y‖μ_z) + D(μ_z‖μ_y) ≤ L‖y − z‖₂² + (√𝔢(T; y) + √𝔢(T; z))‖y − z‖₂`.

**Formalization Note.** `μ_y = tilt μ y`, `E`/`Var` are `lawMean`/`lawVar`, `D` is `lawKL`; fields are
vectors of `EuclideanSpace ℝ (Fin n)` (Euclidean norm), passed to `tilt` through `WithLp.ofLp`. -/
theorem lemma_6_3 (n : ℕ) (hn : 2 ≤ n) (μ : Spin n → ℝ) (hμ : IsFullSupportLaw μ) :
    (∀ (y z : EuclideanSpace ℝ (Fin n)) (f : Spin n → ℝ),
      |lawMean (tilt μ (WithLp.ofLp y)) f - lawMean (tilt μ (WithLp.ofLp z)) f| ^ 2 ≤
        2 * (Real.exp ((lawKL (tilt μ (WithLp.ofLp y)) (tilt μ (WithLp.ofLp z)) +
            lawKL (tilt μ (WithLp.ofLp z)) (tilt μ (WithLp.ofLp y))) / 2) - 1) *
          (lawVar (tilt μ (WithLp.ofLp y)) f + lawVar (tilt μ (WithLp.ofLp z)) f)) ∧
    (∀ (T L : ℝ) (e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ), 0 < T → 0 < L →
      IsCostFn T n e → HasLipCost T L (postMean μ) e →
      ∀ y z : EuclideanSpace ℝ (Fin n),
        lawKL (tilt μ (WithLp.ofLp y)) (tilt μ (WithLp.ofLp z)) +
            lawKL (tilt μ (WithLp.ofLp z)) (tilt μ (WithLp.ofLp y)) ≤
          L * ‖y - z‖ ^ 2 + (Real.sqrt (e T y) + Real.sqrt (e T z)) * ‖y - z‖) := by sorry

end SKWeakPoincare
