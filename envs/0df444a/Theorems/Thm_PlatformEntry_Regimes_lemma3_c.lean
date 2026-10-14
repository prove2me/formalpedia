-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_lemma3_c
-- name    : PlatformEntry.Regimes.lemma3_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:44.798829+00:00
-- url     : https://prove2.me/theorems/28a1d67e-5262-41f5-9774-acd43d0d3239
-- title:
--   Lemma 3(c), PDF p. 32 — for given δ and f, (11) is positive iff β < β₁(δ,f) or β > β₂(δ,f), β₁ ≤ β₂
-- statement:
--   Let $P_{11}(\delta,f,\beta)$ be the function (11),
--   $$P_{11} = -\beta^4(1+f)^2 + 8\delta(1+\delta f) + 2\beta^3(1+f)(1+\delta f) - 4\beta(2+\delta+\delta^2+2\delta f) + \beta^2(-2\delta f + 4(1+f) - 2\delta^2(-1+f^2)).$$
--   For every $\delta \in [0,1]$ and $f \in [0,1)$ there are thresholds $\beta_1(\delta,f) \le \beta_2(\delta,f)$ such that, for every $\beta \in [0,1]$,
--
--   $$
--   P_{11}(\delta,f,\beta) > 0 \iff \beta < \beta_1(\delta,f) \ \text{ or } \ \beta > \beta_2(\delta,f).
--   $$
--
--   So, along the competition intensity, the positivity set of (11) is the complement of a band. The thresholds are defined in the paper's proof; they are stated here as existentials.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, PDF p. 32, Lemma 3 (third clause) and (11); proof PDF p. 33

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem lemma3_c :
    ∀ δ f : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ f → f < 1 →
      ∃ β₁ β₂ : ℝ, β₁ ≤ β₂ ∧
        ∀ β : ℝ, 0 ≤ β → β ≤ 1 → (0 < P11 δ f β ↔ β < β₁ ∨ β₂ < β) := by sorry

end PlatformEntry.Regimes
