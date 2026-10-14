-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_lemma3_a
-- name    : PlatformEntry.Regimes.lemma3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:46.84713+00:00
-- url     : https://prove2.me/theorems/42eb69fa-ea40-471f-8d10-88dd8834148b
-- title:
--   Lemma 3(a), PDF p. 32 — for given f and β, (11) is positive iff δ > δ̃(f,β)
-- statement:
--   Let
--   $$P_{11}(\delta,f,\beta) = -\beta^4(1+f)^2 + 8\delta(1+\delta f) + 2\beta^3(1+f)(1+\delta f) - 4\beta(2+\delta+\delta^2+2\delta f) + \beta^2(-2\delta f + 4(1+f) - 2\delta^2(-1+f^2))$$
--   be the function (11). For every $f \in [0,1)$ and $\beta \in [0,1]$ there is a threshold $\tilde\delta(f,\beta)$ such that, for every $\delta \in [0,1]$,
--
--   $$
--   P_{11}(\delta,f,\beta) > 0 \iff \delta > \tilde\delta(f,\beta).
--   $$
--
--   The threshold is defined in the paper's proof as the smaller root of a quadratic, or as a value bigger than 1 when no root exists; it is stated here as an existential.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, PDF p. 32, Lemma 3 (first clause) and (11); proof PDF pp. 32–33

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem lemma3_a :
    ∀ f β : ℝ, 0 ≤ f → f < 1 → 0 ≤ β → β ≤ 1 →
      ∃ δt : ℝ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → (0 < P11 δ f β ↔ δt < δ) := by sorry

end PlatformEntry.Regimes
