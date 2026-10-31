-- Prove2me | Theorems.Thm_TechBreakthrough_lemma_2
-- name    : TechBreakthrough.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:22.878425+00:00
-- url     : https://prove2.me/theorems/c449888c-9160-4417-870a-f5163bd5901d
-- title:
--   Lemma 2 — the change of variables (22)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`).
--
--   Let $(x,m)\in J$ and let $\tau$ be a stopping time. Then, almost surely, both sides are finite and
--
--   $$\int_m^{M_\tau}e^{-r\tau(y)}G(y)f(y)\,dy=\int_0^\tau e^{-rt}G(M_t)f(M_t)\,dM_t.$$
--
--   The identity turns the integral against $M$ into a sum over levels, which is how the breakthrough integral arises from the threshold $Y$.
--
--   **Formalization Note** Since $M_\tau$ may equal $\beta$ on $\{\tau=\infty\}$, the $y$-integral runs over the $y\in\mathcal I$ with $m<y\le M_\tau$, and $M_\tau$ is an extended real. $e^{-r\infty}=0$.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - encoding: stopping times in T_{X,M} and expectation E_{x,m} under the law of (X, M) → stopping times in T_X under P x, with M = runningMax m a function of the path; reason: p.13: every element of T_{X,M} is P_{x,m}-a.s. in T_X, and M is a function of X and m; same values
--   - encoding: the Stieltjes integral ∫_0^τ … dM_t → the integral over (0, τ], or (0, ∞) when τ = ∞, against the Stieltjes measure of t ↦ M_{t∨0}; reason: M is continuous and nondecreasing, so the measure has no atoms; same value
--   - encoding: ∫_m^{M_τ} with M_τ real → the integral over {y ∈ 𝓘 : m < y, y ≤ M_τ}, with M_τ in EReal; reason: M_τ may be β on {τ = ∞}; same integral
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Lemma 2 (22), p.14; finiteness of (24), p.15

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_stopRegion
import Definitions.Def_TechBreakthrough_Model_hitTransform

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Lemma 2, the change of variables (22), arXiv:2106.05112v1, p.14: for each stopping time `τ`,
`P_x`-almost surely both sides are finite and
`∫_m^{M_τ} e^{−rτ(y)} G(y) f(y) dy = ∫_0^τ e^{−rt} G(M_t) f(M_t) dM_t`.

**Formalization Note** The integral in `y` runs over the `y ∈ 𝓘` with `m < y ≤ M_τ`, because
`M_τ` may equal `β` on `{τ = ∞}`. Finiteness is the proof's claim on (24), p.15, and is stated
as integrability of both integrands. `e^{−r∞} = 0`. -/
theorem lemma_2 (M : Model) (hM : M.Valid) {x m : ℝ} (hz : (x, m) ∈ M.domain)
    {τ : M.Ω → WithTop ℝ≥0} (hτ : τ ∈ M.T) :
    ∀ᵐ ω ∂M.P x,
      IntegrableOn
        (fun y => discountedAt M.r (fun _ => 1) (M.hitTime ω y) * M.G y * M.f y)
        {y ∈ M.I | m < y ∧ (y : EReal) ≤ M.maxAt m τ ω} ∧
      IntegrableOn (M.flow m ω) (Model.elapsed (τ ω)) (dMax m ω) ∧
      ∫ y in {y ∈ M.I | m < y ∧ (y : EReal) ≤ M.maxAt m τ ω},
          discountedAt M.r (fun _ => 1) (M.hitTime ω y) * M.G y * M.f y =
        ∫ t in Model.elapsed (τ ω), M.flow m ω t ∂(dMax m ω) := by sorry

end TechBreakthrough
