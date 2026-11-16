-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_6_4
-- name    : StochAutoreg.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:27:16.551091+00:00
-- url     : https://prove2.me/theorems/f14f70ea-f2b9-4a86-98fb-b3107480f480
-- title:
--   Theorem 6.4 — a finite class with $m_{\mathrm{CoT}}(\varepsilon)=\Theta(LM/\varepsilon)=m_{\mathrm{base}}(\kappa\varepsilon/M)$
-- statement:
--   There is a universal $\kappa>0$ such that for every real $L\ge1$, every integer $M\ge2$ and all sufficiently small $\varepsilon>0$, some finite class $\mathcal F$ satisfies
--
--   $$m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon)=\Theta(LM/\varepsilon),\qquad m^{\mathcal F}_{\mathrm{base}}(\kappa\varepsilon/M)=\Theta(LM/\varepsilon),$$
--
--   at confidence $2/3$. Precisely: there are universal constants $0<c\le C$ such that for all $L\ge1$ and $M\ge2$ there is $\varepsilon_1>0$ with the following property: for every $0<\varepsilon\le\varepsilon_1$ there is a finite class whose two complexities are natural numbers between $c\,LM/\varepsilon$ and $C\,LM/\varepsilon$.
--
--   So the comparison of Theorem 5.1 can be tight: the base and chain-of-thought sample costs can match at any prescribed scale.
--
--   Differences from the source:
--   - encoding: m(ε) with δ omitted → m(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - reading: Θ(LM/ε) and "all sufficiently small ε" → universal constants 0 < c, C quantified with κ before L, M, ε; a threshold ε₁ > 0 depending on L, M; the class last; c·LM/ε ≤ m ≤ C·LM/ε; reason: Θ without subscript has universal constants; two-sided bounds make both complexities finite natural numbers
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 6.4, p.13

import Mathlib
import Definitions.Def_StochAutoreg_mBase
import Definitions.Def_StochAutoreg_mCoT

namespace StochAutoreg

namespace Supplement

/-- **Theorem 6.4** (matching base and CoT costs). For a universal `κ > 0`, every real `L ≥ 1`, integer
`M ≥ 2`, and all sufficiently small `ε > 0`, some finite class satisfies
`m^{F,M}_CoT(ε) = Θ(LM/ε)` and `m^F_base(κε/M) = Θ(LM/ε)`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 6.4, p.13.

**Formalization Note.** Confidence `δ = 1/3`. `Θ` has universal constants `0 < c ≤ C`, quantified with
`κ` before `L, M, ε`; "all sufficiently small `ε`" is a threshold `ε₁ > 0` depending on `L, M`; the
class comes last. Both complexities are then natural numbers (four inequalities). -/
theorem theorem_6_4 :
    ∃ κ : ℝ, 0 < κ ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ L : ℝ, 1 ≤ L → ∀ M : ℕ, 2 ≤ M → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
        ∃ F : Set Generator, F.Finite ∧ ∃ a b : ℕ,
          mCoT F M ε (1 / 3) = a ∧ mBase F (κ * ε / M) (1 / 3) = b ∧
          c * (L * M / ε) ≤ a ∧ (a : ℝ) ≤ C * (L * M / ε) ∧
          c * (L * M / ε) ≤ b ∧ (b : ℝ) ≤ C * (L * M / ε) := by sorry

end Supplement

end StochAutoreg
