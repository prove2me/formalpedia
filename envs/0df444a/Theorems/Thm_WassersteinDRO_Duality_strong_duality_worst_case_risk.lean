-- Prove2me | Theorems.Thm_WassersteinDRO_Duality_strong_duality_worst_case_risk
-- name    : WassersteinDRO.Duality.strong_duality_worst_case_risk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T02:21:10.368698+00:00
-- url     : https://prove2.me/theorems/48a9c57e-491d-49de-b0ab-ac17ab5e743e
-- title:
--   Theorem 7 — strong duality for the worst-case risk
-- statement:
--   For any fixed bounded continuous loss function $\ell$ on $E$, closed nonempty support
--   set $\Xi$, exponent $p \in [1,\infty)$ and radius $\varepsilon \ge 0$, the worst-case risk
--   over the type-$p$ Wasserstein ambiguity set around $\hat P_N$ satisfies
--   $$R_{\varepsilon,p}(\hat P_N,\ell) = \inf_{\gamma \ge 0}\ \mathbb{E}_{\hat P_N}[\ell_\gamma(\xi)] + \gamma\varepsilon^p,$$
--   where $\ell_\gamma(\xi) = \sup_{z\in\Xi} \ell(z) - \gamma\|z-\xi\|^p$ is the Moreau-Yosida
--   regularization of $\ell$. This identifies the right-hand side as the strong Lagrangian
--   dual of the worst-case risk evaluation problem, with $\gamma$ the multiplier of the
--   Wasserstein constraint. The loss function is restricted to bounded continuous $\ell$
--   (rather than the paper's general upper-semicontinuous, $\hat P_N$-integrable $\ell \in
--   \mathcal{L}$, Assumption 1, p. 9) so the Moreau-Yosida regularization is a finite real
--   number pointwise, keeping the right-hand side's Bochner integral well-posed. $\hat P_N$ is
--   itself assumed supported on $\Xi$ (the paper's own standing convention for the nominal
--   distribution): together with $\ell$ bounded, this makes $\ell_\gamma$ bounded on the
--   full-measure set $\Xi$ — bounded above by $\sup\ell$ unconditionally, and bounded below by
--   $\ell(\xi)$ itself via $z=\xi$ whenever $\xi\in\Xi$ — so the integral never silently reduces
--   to Mathlib's non-integrable junk value $0$.
-- source:
--   Kuhn et al. 2019, Theorem 7, p. 10, eq. (10)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_WassersteinDRO_Duality_moreauYosida
import Definitions.Def_WassersteinDRO_Duality_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 7 (Strong duality), Kuhn et al. 2019, p. 10, eq. (10) — the goal theorem: the
worst-case risk (6) of any fixed `ℓ ∈ L` satisfies
`Rε,p(PN,ℓ) = inf_{γ≥0} E_{PN}[ℓγ(ξ)] + γεᵖ`, where `ℓγ(ξ) = sup_{z∈Ξ} ℓ(z) - γ‖z-ξ‖^p` is a
Moreau-Yosida regularization of `ℓ`. The loss function is restricted to bounded continuous
`ℓ : BoundedContinuousFunction E ℝ` (see `Def_WassersteinDRO_Duality_moreauYosida`) rather than the paper's general
upper-semicontinuous, `PN`-integrable `ℓ ∈ L` (Assumption 1, p. 9): this is what keeps the
Moreau-Yosida regularization a finite real number pointwise, so the right-hand side's Bochner
integral is well-posed without extended-real integration machinery. `Ξ.Nonempty` and `IsClosed Ξ`
match the paper's own standing assumption (PDF p. 6) that `Ξ` is a closed set containing the
support of the underlying distribution. `hPNΞ : PN Ξᶜ = 0` states that `PN` itself is supported
on `Ξ` (the same "supported on `Ξ`" convention `Def_WassersteinDRO_Duality_ambiguitySet` uses for
`Q ∈ P(Ξ)`), which the paper's framework presupposes for the nominal distribution throughout §2;
it is what makes `fun x => moreauYosida Ξ ℓ p γ x` genuinely `PN`-integrable and hence the
right-hand side well-posed: for `PN`-a.e. `x` (i.e. every `x ∈ Ξ`), taking `z := x` in the
defining supremum gives `moreauYosida Ξ ℓ p γ x ≥ ℓ x - γ·0 = ℓ x ≥ -‖ℓ‖`, while
`moreauYosida Ξ ℓ p γ x ≤ ⨆ z, ℓ z ≤ ‖ℓ‖` unconditionally (from `ℓ` bounded and `γ ≥ 0`), so the
integrand is bounded on the full-measure set `Ξ`, avoiding the case (an unbounded `Ξ` together
with a `PN` whose support strays outside it) where the Bochner integral would silently be `0`. -/
theorem strong_duality_worst_case_risk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞne : Ξ.Nonempty) (hΞcl : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN] (hPNΞ : PN Ξᶜ = 0)
    (ℓ : BoundedContinuousFunction E ℝ) :
    worstCaseRisk ε p Ξ PN (ℓ : E → ℝ) =
      ⨅ (γ : ℝ) (_ : 0 ≤ γ),
        ((∫ x, moreauYosida Ξ ℓ p γ x ∂PN : ℝ) : EReal) +
          ((ENNReal.ofReal (γ * ε ^ p) : ENNReal) : EReal) := by sorry

end WassersteinDRO.Duality
