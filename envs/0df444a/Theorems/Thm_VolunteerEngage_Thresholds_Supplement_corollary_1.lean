-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_Supplement_corollary_1
-- name    : VolunteerEngage.Thresholds.Supplement.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:13:46.983799+00:00
-- url     : https://prove2.me/theorems/67b181b2-1e57-439b-b11f-608bb9e6d8f1
-- title:
--   Corollary 1, p. 22 — the integral of v solves all of (59)–(60)
-- statement:
--   Let $(\beta,v)$ be a solution of (68)–(69) under the model's standing assumptions, and let $v'$ denote its continuous derivative. Set $f(z)=\int_0^zv(s)\,ds-pz$. Then $\beta>0$, $f$ is twice continuously differentiable on $[0,\infty)$ with $f'=v-p$ and $f''=v'$, and
--
--   $$\beta=\min_{x\in A}\left\{\frac{\sigma^2}{2}f''(w)+(x-\kappa w)f'(w)+c(x)\right\},\qquad w\ge0.$$
--
--   The minimum is attained for every $w$. In addition, $f'(0)=-p$, $f'$ is strictly increasing, and $f'(w)\to0$ as $w\to\infty$. This is the complete original Bellman equation used for verification of Theorem 2.
--
--   Differences from the source:
--   - encoding: the queueing primitives and standing assumptions of §§2–3 → M.Standing at every theorem; reason: it expands to L≥1, θ0<0, η_l>0, 0<c_1<⋯<c_L<p and p,κ,σ>0; these are the inherited model assumptions, with no θ_L≥0 restriction
--   - generalization: the solution (β*,v) obtained in Theorem 1 → every solution of the published IsBellmanSol; reason: the conclusions use only (68)–(69), and specialize to the solution furnished by Theorem 1
--   - encoding: derivatives on [0,∞) → explicit derivatives within [0,∞), including at zero; reason: the source specifies only this domain; one-sided derivatives prevent an arbitrary extension from affecting the endpoint
--   - encoding: min in (59) → IsLeast of the image of A; reason: retains attainment as well as the lower-bound property
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, pp. 20, 22, (59)–(60), Corollary 1

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_RelativeValue
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_BellmanF

namespace VolunteerEngage.Thresholds.Supplement

/-- Corollary 1, p. 22: all of (59)–(60), including an attained minimum. -/
theorem corollary_1 (M : Model) (hM : M.Standing) (β : ℝ) (v v' : ℝ → ℝ)
    (hv : IsBellmanSol M β v v') :
    IsFBellmanSol M β (relativeValue M v) (fun z => v z - M.p) v' := by sorry

end VolunteerEngage.Thresholds.Supplement
