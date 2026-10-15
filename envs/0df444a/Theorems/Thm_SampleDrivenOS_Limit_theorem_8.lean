-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_theorem_8
-- name    : SampleDrivenOS.Limit.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:25.385559+00:00
-- url     : https://prove2.me/theorems/3b5e764b-45bc-4469-9c9d-5f6ba2068ff4
-- title:
--   Theorem 8 — $0\le\tilde\alpha(p)\le\alpha(p)\le\alpha^*$, and $\tilde\alpha(p),\alpha(p)\to\alpha^*$ as $p\to1$
-- statement:
--   Let $\alpha^*\in(0,1)$ solve
--   $$\int_0^1\frac{dy}{y(1-\ln y)+1/\alpha^*-1}=1$$
--   (the i.i.d. prophet constant, $\alpha^*\approx0.745$), let $\tilde\alpha(p)$ be the root of (19) given by Lemma 7 for each $p\in(0,1)$, and let $\alpha(p)$ be the optimal value of SDCLP$_p$. Then:
--   1. for every $p\in(0,1)$,
--   $$0\le\tilde\alpha(p)\le\alpha(p)\le\alpha^*;$$
--   2. as $p\to1^-$,
--   $$\tilde\alpha(p)\to\alpha^*\qquad\text{and}\qquad\alpha(p)\to\alpha^*,$$
--   that is, defining $\tilde\alpha(1)$ and $\alpha(1)$ by continuity, $\tilde\alpha(1)=\alpha(1)=\alpha^*$.
--
--   In the sample-driven optimal stopping model, $\alpha(p)$ is the optimal competitive ratio when a fraction $p$ of the items is observed as samples, so the theorem says that with almost all information the best guarantee approaches the i.i.d. prophet constant, and that the explicit rule of Lemma 6 is asymptotically optimal.
--
--   **Formalization Note** $\tilde\alpha$ and $\alpha^*$ enter through predicates: the statement holds for every function $\tilde\alpha$ picking a root of (19) at each $p\in(0,1)$ and every solution $\alpha^*\in(0,1)$ of the integral equation (existence and uniqueness of $\alpha^*$ is the separate open item `CorreaThreshold.Adaptive.beta_star_existsUnique`, with $\beta=1/\alpha^*$). The limits are one-sided, $p\to1^-$. The bound $\alpha(p)\le\alpha^*$ is not proved in the paper; it is imported from the i.i.d. prophet inequality literature through the interpretation of $\alpha(p)$ as a competitive ratio (§4.1–4.2), which is not formalized here.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 17, Theorem 8 and the sentence preceding it

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Theorem 8 (p. 17): for every `p ∈ (0, 1)`, `0 ≤ α̃(p) ≤ α(p) ≤ α*`; moreover `α̃(p)` and `α(p)`
both tend to `α*` as `p → 1` from below (`α̃(1) = α(1) = α*`). Here `α̃(p)` is the root of (19)
(Lemma 7), `α(p)` the optimal value of SDCLP_p, and `α*` the solution of
`∫_0^1 1 / (y(1 - ln y) + 1/α* - 1) dy = 1`. -/
theorem theorem_8 (s : ℝ) (hs : IsAlphaStar s) (aT : ℝ → ℝ)
    (haT : ∀ p ∈ Set.Ioo (0:ℝ) 1, IsAlphaTilde p (aT p)) :
    (∀ p ∈ Set.Ioo (0:ℝ) 1, 0 ≤ aT p ∧ aT p ≤ sdclpValue p ∧ sdclpValue p ≤ s) ∧
      Tendsto aT (𝓝[<] 1) (𝓝 s) ∧ Tendsto sdclpValue (𝓝[<] 1) (𝓝 s) := by sorry

end SampleDrivenOS.Limit
