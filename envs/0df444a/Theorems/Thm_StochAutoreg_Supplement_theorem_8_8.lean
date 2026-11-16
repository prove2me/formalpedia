-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_8_8
-- name    : StochAutoreg.Supplement.theorem_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:30:51.721058+00:00
-- url     : https://prove2.me/theorems/476c2a4c-c96f-41a8-8223-d1ddf498d282
-- title:
--   Theorem 8.8 — at $M=d^2$: $m_{\mathrm{CoT}}\le\widetilde O(d/\varepsilon)$ and $m_{\mathrm{e2e}}=\widetilde\Theta(d^2/\varepsilon)$
-- statement:
--   For sufficiently large $d$ and sufficiently small $\varepsilon$, at horizon $M=d^2$,
--
--   $$m^{\mathcal F_\sigma(d),d^2}_{\mathrm{CoT}}(\varepsilon)\le\widetilde O(d/\varepsilon),\qquad m^{\mathcal F_\sigma(d),d^2}_{\mathrm{e2e}}(\varepsilon)=\widetilde\Theta(d^2/\varepsilon),$$
--
--   where only logarithms in $d$ and $1/\varepsilon$ are suppressed, and the complexities are at confidence $2/3$. Precisely: with $\Lambda=1+\log d+\log(1/\varepsilon)$, there are a universal $C>0$, an exponent $k\in\mathbb N$ and thresholds $d_0$, $\varepsilon_0>0$ such that for all $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$, both complexities are finite and
--
--   $$m_{\mathrm{CoT}}\le C\,\frac d\varepsilon\,\Lambda^k,\qquad \frac{d^2/\varepsilon}{C\Lambda^k}\le m_{\mathrm{e2e}}\le C\,\frac{d^2}\varepsilon\,\Lambda^k .$$
--
--   This is the statistical separation between chain-of-thought and end-to-end supervision for the logistic class: a factor of about $d$.
--
--   Differences from the source:
--   - encoding: m(ε) with δ omitted → m(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - reading: Õ(·), Θ̃(·), "only logarithms in d and 1/ε are suppressed", "sufficiently large d and sufficiently small ε" → a factor C·Λ^k with Λ = 1 + log d + log(1/ε), universal C and k; independent thresholds d₀ and ε₀; Θ̃ as the two-sided bound; reason: the suppressed factors are polylogarithmic in d and 1/ε, as the theorem says
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 8.8, p.20

import Mathlib
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_mE2E
import Definitions.Def_StochAutoreg_Supplement_logisticClass

namespace StochAutoreg

namespace Supplement

/-- **Theorem 8.8** (statistical separation at `M = d²`). For sufficiently large `d` and sufficiently small
`ε`, at `M = d²`, `m^{F_σ(d),d²}_CoT(ε) ≤ Õ(d/ε)` and `m^{F_σ(d),d²}_e2e(ε) = Θ̃(d²/ε)`. Only logarithms in
`d` and `1/ε` are suppressed.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 8.8, p.20.

**Formalization Note.** Confidence `δ = 1/3`. `Õ`/`Θ̃` with only logarithms in `d` and `1/ε` suppressed:
a universal constant `C > 0` and power `k` of `Λ = 1 + log d + log(1/ε)`, with independent thresholds
`d₀` and `ε₀`. The CoT complexity is at most `C(d/ε)Λ^k`; the e2e complexity is between
`(d²/ε)/(CΛ^k)` and `C(d²/ε)Λ^k`. Both are asserted finite. -/
theorem theorem_8_8 :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ d₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        (∃ a : ℕ, mCoT (logisticClass d) (d ^ 2) ε (1 / 3) = a ∧
          (a : ℝ) ≤ C * (d / ε) * (1 + Real.log d + Real.log (1 / ε)) ^ k) ∧
        (∃ b : ℕ, mE2E (logisticClass d) (d ^ 2) ε (1 / 3) = b ∧
          (d : ℝ) ^ 2 / ε ≤ C * (1 + Real.log d + Real.log (1 / ε)) ^ k * b ∧
          (b : ℝ) ≤ C * ((d : ℝ) ^ 2 / ε) * (1 + Real.log d + Real.log (1 / ε)) ^ k) := by sorry

end Supplement

end StochAutoreg
