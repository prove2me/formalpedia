-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_8_5
-- name    : StochAutoreg.Supplement.theorem_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:29:00.112545+00:00
-- url     : https://prove2.me/theorems/2572a045-962d-4a8d-acd5-b611292d65f8
-- title:
--   Theorem 8.5 — end-to-end upper bound for the logistic class $\mathcal F_\sigma(d)$
-- statement:
--   There is a universal constant $C>0$ such that for $d,M\ge1$ and $0<\varepsilon<1$,
--
--   $$m^{\mathcal F_\sigma(d),M}_{\mathrm{e2e}}(\varepsilon)\le\frac C\varepsilon\Bigl[d^2\log(d+1)+d\log\frac{CM}\varepsilon\Bigr],$$
--
--   and for $0<\delta<1/2$, at confidence $1-\delta$,
--
--   $$m^{\mathcal F_\sigma(d),M}_{\mathrm{e2e}}(\varepsilon,\delta)\le\frac{C\log(C/\varepsilon)}\varepsilon\Bigl[d^2\log(d+1)+d\log\frac{CM}\varepsilon+\log\frac1\delta\Bigr].$$
--
--   Here $\mathcal F_\sigma(d)$ is the class of all affine logistic generators of memory $d$ with unbounded real parameters, the first bound is at confidence $2/3$, and logarithms are natural. Although the class is infinite and unbounded, end-to-end learning needs only about $d^2/\varepsilon$ samples.
--
--   **Formalization Note** One constant $C$ serves both displays (a larger $C$ only weakens each bound, so this is no restriction); both complexities are asserted to be natural numbers.
--
--   Differences from the source:
--   - encoding: m(ε) with δ omitted → m(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - encoding: C in each display → one universal C for both displays; reason: both right sides increase with C (for M ≥ 1, ε < 1, the logarithms are positive once C ≥ 1), so two constants can be replaced by their maximum
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 8.5, p.19

import Mathlib
import Definitions.Def_StochAutoreg_mE2E
import Definitions.Def_StochAutoreg_Supplement_logisticClass

namespace StochAutoreg

namespace Supplement

/-- **Theorem 8.5** (end-to-end upper bound for the logistic class). For `d, M ≥ 1` and `0 < ε < 1`,
`m^{F_σ(d),M}_e2e(ε) ≤ (C/ε)[d² log(d+1) + d log(CM/ε)]`. For `0 < δ < 1/2`, the bound at confidence
`1 − δ` is `m^{F_σ(d),M}_e2e(ε, δ) ≤ (C log(C/ε)/ε)[d² log(d+1) + d log(CM/ε) + log(1/δ)]`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 8.5, p.19.

**Formalization Note.** One universal `C > 0` for both displays, before `d, M, ε, δ` (a larger `C`
only enlarges both right sides, so one constant is no restriction). The first display is at
`δ = 1/3`. Natural logarithms. Both complexities are asserted finite (natural numbers). -/
theorem theorem_8_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ M : ℕ, 1 ≤ M → ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∃ k : ℕ, mE2E (logisticClass d) M ε (1 / 3) = k ∧
        (k : ℝ) ≤ C / ε * ((d : ℝ) ^ 2 * Real.log (d + 1) + d * Real.log (C * M / ε))) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ k : ℕ, mE2E (logisticClass d) M ε δ = k ∧
          (k : ℝ) ≤ C * Real.log (C / ε) / ε *
            ((d : ℝ) ^ 2 * Real.log (d + 1) + d * Real.log (C * M / ε) + Real.log (1 / δ)) := by sorry

end Supplement

end StochAutoreg
