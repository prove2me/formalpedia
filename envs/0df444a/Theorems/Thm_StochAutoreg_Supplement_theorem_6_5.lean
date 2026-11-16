-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_6_5
-- name    : StochAutoreg.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:27:56.798237+00:00
-- url     : https://prove2.me/theorems/2c8a2a47-d6ef-444d-8900-231c9b5d2528
-- title:
--   Theorem 6.5 — a finite class with $m_{\mathrm{CoT}}(\rho\varepsilon)=\Theta_\rho(N)$ and $m_{\mathrm{e2e}}(\varepsilon)=\Theta(NM/\varepsilon)$
-- statement:
--   For fixed $0<\rho\le1$, integers $N\ge1$, $M\ge2$, and all sufficiently small $\varepsilon>0$, there exists a finite class $\mathcal F$ with
--
--   $$m^{\mathcal F,M}_{\mathrm{CoT}}(\rho\varepsilon)=\Theta_\rho(N),\qquad m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon)=\Theta(NM/\varepsilon),$$
--
--   at confidence $2/3$. Precisely: there are universal constants $c_2,C_2>0$ and, for each $\rho$, constants $c_1,C_1>0$ depending only on $\rho$, such that for all $N\ge1$, $M\ge2$ there is $\varepsilon_1>0$ with: for every $0<\varepsilon\le\varepsilon_1$ one finite class has $c_1N\le m_{\mathrm{CoT}}(\rho\varepsilon)\le C_1N$ and $c_2NM/\varepsilon\le m_{\mathrm{e2e}}(\varepsilon)\le C_2NM/\varepsilon$.
--
--   The factor $M/\varepsilon$ of Theorem 5.2 is therefore attained, even when chain-of-thought learning is evaluated at the smaller accuracy $\rho\varepsilon$.
--
--   Differences from the source:
--   - encoding: m(ε) with δ omitted → m(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - reading: Θ_ρ(N), Θ(NM/ε) and "all sufficiently small ε" → universal c₂, C₂ first; c₁, C₁ after ρ and before N, M, ε; a threshold ε₁ after ρ, N, M; one finite class for both; two-sided bounds on natural numbers; reason: Θ_ρ means constants depending on ρ only, Θ universal constants
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 6.5, p.14

import Mathlib
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_mE2E

namespace StochAutoreg

namespace Supplement

/-- **Theorem 6.5** (the factor `M/ε` in Theorem 5.2). For fixed `0 < ρ ≤ 1`, integers `N ≥ 1`,
`M ≥ 2`, and all sufficiently small `ε > 0`, there exists a finite class with
`m^{F,M}_CoT(ρε) = Θ_ρ(N)` and `m^{F,M}_e2e(ε) = Θ(NM/ε)`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 6.5, p.14.

**Formalization Note.** Confidence `δ = 1/3`. The `Θ(NM/ε)` constants `c₂, C₂` are universal (first);
the `Θ_ρ(N)` constants `c₁, C₁` depend on `ρ` only (after `ρ`, before `N, M, ε`); the threshold `ε₁`
depends on `ρ, N, M`; one finite class satisfies both. Both complexities are natural numbers. -/
theorem theorem_6_5 :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
        ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ, 2 ≤ M → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
          ∃ F : Set Generator, F.Finite ∧ ∃ a b : ℕ,
            mCoT F M (ρ * ε) (1 / 3) = a ∧ mE2E F M ε (1 / 3) = b ∧
            c₁ * N ≤ a ∧ (a : ℝ) ≤ C₁ * N ∧
            c₂ * (N * M / ε) ≤ b ∧ (b : ℝ) ≤ C₂ * (N * M / ε) := by sorry

end Supplement

end StochAutoreg
