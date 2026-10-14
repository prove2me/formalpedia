-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_lemma3_b
-- name    : PlatformEntry.Regimes.lemma3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:49.397982+00:00
-- url     : https://prove2.me/theorems/3abc1dcf-4666-4a49-8402-92894352fb48
-- title:
--   Lemma 3(b), PDF p. 32 — for given δ and β, (11) is positive iff f > f̃(δ,β)
-- statement:
--   Let $P_{11}(\delta,f,\beta)$ be the function (11),
--   $$P_{11} = -\beta^4(1+f)^2 + 8\delta(1+\delta f) + 2\beta^3(1+f)(1+\delta f) - 4\beta(2+\delta+\delta^2+2\delta f) + \beta^2(-2\delta f + 4(1+f) - 2\delta^2(-1+f^2)).$$
--   For every $\delta \in [0,1]$ and $\beta \in [0,1]$ there is a threshold $\tilde f(\delta,\beta)$ such that, for every $f \in [0,1)$,
--
--   $$
--   P_{11}(\delta,f,\beta) > 0 \iff f > \tilde f(\delta,\beta).
--   $$
--
--   The threshold is defined in the paper's proof; it is stated here as an existential.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, PDF p. 32, Lemma 3 (second clause) and (11); proof PDF p. 33

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem lemma3_b :
    ∀ δ β : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ β → β ≤ 1 →
      ∃ ft : ℝ, ∀ f : ℝ, 0 ≤ f → f < 1 → (0 < P11 δ f β ↔ ft < f) := by sorry

end PlatformEntry.Regimes
