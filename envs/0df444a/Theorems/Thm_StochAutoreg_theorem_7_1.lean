-- Prove2me | Theorems.Thm_StochAutoreg_theorem_7_1
-- name    : StochAutoreg.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:00.617198+00:00
-- url     : https://prove2.me/theorems/0a7c33f3-61f4-4cfb-88e9-cbb7eef40e50
-- title:
--   Theorem 7.1 — simultaneous exact-accuracy separation: one finite class with $m_{\mathrm{CoT}}/m_{\mathrm{base}}>AM/\varepsilon$ and $m_{\mathrm{e2e}}/m_{\mathrm{CoT}}>AM/\varepsilon$
-- statement:
--   A stochastic generator assigns a Bernoulli next-token law to every binary string and is iterated $M$ times from a prompt. Write $m^{\mathcal F}_{\mathrm{base}}(\varepsilon)$, $m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon)$, $m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon)$ for the sample complexities at confidence $2/3$, in forward KL, uniformly over the prompt law and the target in $\mathcal F$, under one-step, full-trajectory and final-token supervision.
--
--   There are universal $M_0$ and $\varepsilon_0>0$ such that, for every $M\ge M_0$, $0<\varepsilon\le\varepsilon_0$ and $A\ge1$, a finite class $\mathcal F$ satisfies $0<m^{\mathcal F}_{\mathrm{base}}(\varepsilon)<\infty$ and
--
--   $$\frac{m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon)}{m^{\mathcal F}_{\mathrm{base}}(\varepsilon)}>\frac{AM}\varepsilon,\qquad\frac{m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon)}{m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon)}>\frac{AM}\varepsilon.$$
--
--   So at one and the same accuracy, neither richer supervision nor one-step learnability controls the next complexity by any function of $M$ and $\varepsilon$ alone.
--
--   Differences from the source:
--   - reading: 0 < m_base(ε) < ∞ and ratios of the complexities → all three complexities are natural numbers, m_base and m_CoT are positive, and the ratios are real quotients; reason: the proof's last line says "Finiteness follows from Proposition 4.2", and this is the stronger reading, excluding ∞/∞ and x/0
--   - encoding: a generator g : Σ⋆ → Δ(Σ) → a map List Bool → unitInterval; reason: a law on {0,1} is its mass at 1; same objects
--   - encoding: "random seeds" → one seed uniform on [0,1]; reason: the paper names no seed space, and a uniform point of [0,1] simulates any standard Borel seed
--   - encoding: a distribution on Σ⋆, the expectation (1.1), i.i.d. samples → PMF (List Bool), a tsum in ℝ≥0∞, a product measure on a countable type; reason: Lean representation of the same quantities; the value +∞ is kept
--   - encoding: m_b(ε), with δ omitted → m_b(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - encoding: universal M₀, with the standing assumption M ≥ 1 → 1 ≤ M₀ written out; reason: the model has M ≥ 1; the paper's M₀ is J + 3
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 7.1, p.14

import Mathlib
import Definitions.Def_StochAutoreg_Generator
import Definitions.Def_StochAutoreg_mBase
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_mE2E

namespace StochAutoreg

/-- **Theorem 7.1** (simultaneous exact-accuracy separation). There are universal `M₀` and `ε₀ > 0` such that, for every `M ≥ M₀`, `0 < ε ≤ ε₀`
and `A ≥ 1`, a finite class `F` satisfies `0 < m^F_base(ε) < ∞` and
`m^{F,M}_CoT(ε)/m^F_base(ε) > AM/ε`, `m^{F,M}_e2e(ε)/m^{F,M}_CoT(ε) > AM/ε`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 7.1, p.14.

**Formalization Note.** `M₀, ε₀` come before `M, ε, A`, and `F` after all of them. All three complexities are natural numbers, with `m_base, m_CoT`
positive, so both ratios are real quotients; the confidence `δ = 1/3` is written out (p.3 omits it). -/
theorem theorem_7_1 :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 1 ≤ A →
        ∃ F : Set Generator, F.Finite ∧ ∃ a b c : ℕ,
          mBase F ε (1 / 3) = a ∧ mCoT F M ε (1 / 3) = b ∧ mE2E F M ε (1 / 3) = c ∧
          0 < a ∧ 0 < b ∧
          A * M / ε < (b : ℝ) / a ∧ A * M / ε < (c : ℝ) / b := by sorry

end StochAutoreg
