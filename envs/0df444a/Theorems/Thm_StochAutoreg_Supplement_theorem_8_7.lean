-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_8_7
-- name    : StochAutoreg.Supplement.theorem_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:29:47.407585+00:00
-- url     : https://prove2.me/theorems/d2c3606b-87b9-4638-882e-3fc1c3f1b05d
-- title:
--   Theorem 8.7 — $m^{\mathcal F_\sigma(d),M}_{\mathrm{e2e}}(\varepsilon)\ge c\,d^2/\varepsilon$ for $M\ge d^2$
-- statement:
--   There are universal constants $c,\varepsilon_0>0$ and $d_0$ such that for every $d\ge d_0$, every horizon $M\ge d^2$ and every $0<\varepsilon\le\varepsilon_0$,
--
--   $$m^{\mathcal F_\sigma(d),M}_{\mathrm{e2e}}(\varepsilon)\ge c\,\frac{d^2}{\varepsilon},$$
--
--   at confidence $2/3$. End-to-end learning of the logistic class at long horizons is thus quadratic in the memory $d$, matching Theorem 8.5 up to logarithms.
--
--   **Formalization Note** The bound is stated for every finite value of the complexity, and holds trivially when it is $+\infty$.
--
--   Differences from the source:
--   - encoding: m(ε) with δ omitted → m(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - encoding: m_e2e(ε) ≥ c d²/ε with m_e2e ∈ {0,…,+∞} → c·d²/ε ≤ n for every finite value n of m_e2e(ε); reason: the value +∞ satisfies the lower bound
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 8.7, p.20

import Mathlib
import Definitions.Def_StochAutoreg_mE2E
import Definitions.Def_StochAutoreg_Supplement_logisticClass

namespace StochAutoreg

namespace Supplement

/-- **Theorem 8.7** (quadratic end-to-end lower bound). There are universal `c, ε₀ > 0` and `d₀` such that
for `d ≥ d₀`, `M ≥ d²` and `0 < ε ≤ ε₀`, `m^{F_σ(d),M}_e2e(ε) ≥ c d²/ε`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 8.7, p.20.

**Formalization Note.** Confidence `δ = 1/3`. Every horizon `M ≥ d²`. The lower bound is stated for
every finite value of the complexity, so `+∞` satisfies it. The cited threshold-shattering result of
[44, Theorem 1] is a proof input, not a hypothesis. -/
theorem theorem_8_7 :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d → ∀ M : ℕ, d ^ 2 ≤ M → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ n : ℕ, mE2E (logisticClass d) M ε (1 / 3) = n → c * (d : ℝ) ^ 2 / ε ≤ n := by sorry

end Supplement

end StochAutoreg
