-- Prove2me | Theorems.Thm_StrategicObfuscation_example_backfire
-- name    : StrategicObfuscation.example_backfire
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:30.316162+00:00
-- url     : https://prove2.me/theorems/5010bf31-0ee8-4028-b84c-4e00cd0fcb97
-- title:
--   §3.1, p.14 — $\pi(\sigma,e)=\sigma q(e)$ satisfies (5) on $(1/2,\bar\sigma_2)$ and the payoff falls (corrected: open at $1/2$)
-- statement:
--   Let $g=1$, $V=6$, $c=1$, $p=1/2$, $\pi(\sigma,e)=\sigma q(e)$, where $q(e)=1-\sqrt{2e}$ for $e\le 1/2$ and $q(e)=0$ otherwise. Then:
--
--   1. $\pi$ is a detection probability, and $e(\alpha,\sigma)=(\alpha\sigma)^2/2$ solves (1);
--   2. $\bar\sigma_1=0$ and $\bar\sigma_2=2\sqrt2-2$;
--   3. the explicit family $(\alpha^*,Q^*)$ is an equilibrium at every $\sigma\in[0,1]$;
--   4. for $\sigma\in(1/2,\bar\sigma_2)$, the left side of (5) equals $1-2\sigma<0$, and $u_S(\sigma)=2+\sigma(1-\sigma)/2$;
--   5. $u_S(0.8)<u_S(0.6)$.
--
--   This is the paper's illustration that condition (5) can hold, and it supplies the instance in which more resources make the sponsor worse off.
--
--   Differences from the source:
--   - reading: the example states no parameters → g = 1, V = 6, c = 1, p = 1/2; reason: g = 1 is what gives the printed 0.5; the other three are chosen with pV > c
--   - reading: (5) holds on [0.5, 0.81] → (5) holds on (1/2, σ̄2) with σ̄2 = 2√2 − 2 ≈ 0.828; reason: 0.81 is presumably σ̄2 for the simulation's unstated parameters; the Lean interval contains every point of (0.5, 0.81]
--   - correction: (5) holds at σ = 0.5 → the interval is open at 1/2; reason: at g = 1 the left side of (5) at σ = 1/2 is 0, so the strict inequality (5) fails there
--   - encoding: Bayes' rule (2) and (4) as quotients → cross-multiplied in IsEquilibrium, with off-path belief 0 at σ = 1; reason: the same equations whenever the denominator is nonzero
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3.1, p.14, with Figure 4b

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibriumFamily
import Definitions.Def_StrategicObfuscation_equilibriumPayoff
import Definitions.Def_StrategicObfuscation_sigmaBarOne
import Definitions.Def_StrategicObfuscation_sigmaBarTwo
import Definitions.Def_StrategicObfuscation_conditionFiveLHS
import Definitions.Def_StrategicObfuscation_examplePi
import Definitions.Def_StrategicObfuscation_exampleEffort
import Definitions.Def_StrategicObfuscation_exampleAlpha
import Definitions.Def_StrategicObfuscation_exampleBelief

open Set

namespace StrategicObfuscation

/-- **The worked example: `π(σ, e) = σ q(e)` satisfies (5) at moderate `σ` and the payoff falls.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3.1, p.14 (PDF p.14), with Figure 4b.

At `g = 1`, `V = 6`, `c = 1`, `p = 1/2`: `π` is a detection probability, `e(α, σ) = (α σ)²/2` solves
(1), `σ̄1 = 0`, `σ̄2 = 2√2 - 2`, `(exampleAlpha, exampleBelief)` is an equilibrium at every
`σ ∈ [0, 1]`, on `(1/2, σ̄2)` the left side of (5) equals `1 - 2σ < 0` and `u_S = 2 + σ(1 - σ)/2`, and
`u_S(0.8) < u_S(0.6)`.

**Formalization Note** The page fixes no parameters. `g = 1` is what produces its `0.5`; `V = 6`, `c = 1`,
`p = 1/2` are chosen here. The printed `[0.5, 0.81]` is read as `(1/2, σ̄2)`, where `σ̄2 ≈ 0.828` for these
parameters: the printed upper end `0.81` lies below it, and at `σ = 1/2` the left side of (5) is `0`, so
the strict inequality (5) fails there. -/
theorem example_backfire :
    IsDetection examplePi ∧
    IsEffort examplePi 1 exampleEffort ∧
    sigmaBarOne exampleEffort = 0 ∧
    sigmaBarTwo examplePi 6 1 (1 / 2) exampleEffort = 2 * Real.sqrt 2 - 2 ∧
    IsEquilibriumFamily examplePi 6 1 (1 / 2) exampleEffort exampleAlpha exampleBelief ∧
    (∀ σ ∈ Ioo (1 / 2 : ℝ) (2 * Real.sqrt 2 - 2),
      conditionFiveLHS examplePi (equilibriumEffort exampleEffort exampleAlpha) σ = 1 - 2 * σ ∧
      1 - 2 * σ < 0 ∧
      equilibriumPayoff examplePi 6 1 (1 / 2) exampleEffort exampleAlpha σ =
        2 + σ * (1 - σ) / 2) ∧
    equilibriumPayoff examplePi 6 1 (1 / 2) exampleEffort exampleAlpha (4 / 5) <
      equilibriumPayoff examplePi 6 1 (1 / 2) exampleEffort exampleAlpha (3 / 5) := by sorry

end StrategicObfuscation
