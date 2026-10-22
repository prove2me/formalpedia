-- Prove2me | Theorems.Thm_RenewForward_PriceImpact_theorem_1
-- name    : RenewForward.PriceImpact.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:43.916901+00:00
-- url     : https://prove2.me/theorems/46da01c0-ce88-49d4-ab56-6dbfe8bbfc80
-- title:
--   Theorem 1, p. 14 — the forward-spot equilibrium exists, is unique, and is f*_Pi = ω/ν, p_f = a_f − 2b_fω/ν, with spot outcome (11)–(12)
-- statement:
--   Under the standing assumptions, fix a wind capacity $k_W \ge 0$ and let $\omega, \nu, a_f, b_f$ be the closed forms (13)–(16) evaluated at the moments of $(\theta, \xi)$.
--
--   1. A triple $(f_{P1}, f_{P2}, p_f)$ is a forward-spot equilibrium if and only if
--   $$f_{P1} = f_{P2} = \frac{\omega}{\nu}, \qquad p_f = a_f - \frac{2 b_f\omega}{\nu}.$$
--   In particular the equilibrium exists and is unique.
--   2. At these forward positions the Lemma 1 spot outcome is, at every realization,
--   $$q^*_{Pi} = \frac{q_0}{3} + \frac{\omega}{3\nu}, \qquad p_s = \frac{p_0}{3} - \frac{2\omega}{3\nu}.$$
--
--   The theorem shows how wind capacity enters spot prices twice: directly through $p_0$ (the merit-order effect) and through the producers' forward positions $\omega/\nu$, which depend on the variance and skewness of wind output.
--
--   **Formalization Note.** An equilibrium is defined by optimality: retailers are price takers, the market clears at $f_P = f_R$, and each producer's deviation is evaluated at the forward price that clears the market at the deviated sales (producers have forward market power). $E[q_0]$ and $E[p_0]$ inside $\omega$ and $a_f$ are written out as $a - c + \mu_\theta - \mu_\xi k_W$ and $a + 2c + \mu_\theta - \mu_\xi k_W$.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), p. 14, Theorem 1, (11)–(16)

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms

namespace RenewForward.PriceImpact

open MeasureTheory ProbabilityTheory

/-- Theorem 1 (Forward-spot equilibrium), p. 14: at every capacity `kW ≥ 0` the forward-spot equilibrium
exists, is unique, and is given by (11)–(16); at it the spot quantities and price are (11)–(12). -/
theorem theorem_1 (M : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ ξ : Ω → ℝ) (hS : Standing M P θ ξ) (kW : ℝ) (hkW : 0 ≤ kW) :
    (∀ f1 f2 pf : ℝ, IsFwdEq M P θ ξ kW f1 f2 pf ↔
      f1 = fStar M (momentsOf P θ ξ) kW ∧ f2 = fStar M (momentsOf P θ ξ) kW ∧
        pf = aF M (momentsOf P θ ξ) kW
          - 2 * bF M (momentsOf P θ ξ) kW * omegaFwd M (momentsOf P θ ξ) kW
            / nuFwd M (momentsOf P θ ξ) kW) ∧
    (∀ w : Ω,
      spotQ M θ ξ kW (fStar M (momentsOf P θ ξ) kW) (fStar M (momentsOf P θ ξ) kW) w
          = q0 M θ ξ kW w / 3
            + omegaFwd M (momentsOf P θ ξ) kW / (3 * nuFwd M (momentsOf P θ ξ) kW) ∧
      spotP M θ ξ kW (fStar M (momentsOf P θ ξ) kW + fStar M (momentsOf P θ ξ) kW) w
          = p0 M θ ξ kW w / 3
            - 2 * omegaFwd M (momentsOf P θ ξ) kW / (3 * nuFwd M (momentsOf P θ ξ) kW)) := by sorry

end RenewForward.PriceImpact
