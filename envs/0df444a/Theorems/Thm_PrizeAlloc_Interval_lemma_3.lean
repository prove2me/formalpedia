-- Prove2me | Theorems.Thm_PrizeAlloc_Interval_lemma_3
-- name    : PrizeAlloc.Interval.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:35.093626+00:00
-- url     : https://prove2.me/theorems/25ee2fa6-909c-406d-b826-9571805f1f5d
-- title:
--   Lemma 3 — two monotone consistent rules that agree on two-competitor competitions agree everywhere
-- statement:
--   Let $\varphi$ and $\varphi'$ be prize allocation rules that both satisfy endowment monotonicity and consistency. If
--   $$\varphi(N, \mathcal R, E) = \varphi'(N, \mathcal R, E) \quad \text{for every competition with } |N| = 2,$$
--   then $\varphi(N, \mathcal R, E) = \varphi'(N, \mathcal R, E)$ for every competition $(N, \mathcal R, E)$, with any number of competitors.
--
--   A consistent, monotone rule is therefore determined by its two-competitor part; in the proof of Theorem 1 this reduces the characterization to competitions with two competitors.
--
--   **Formalization Note** Agreement is stated competitor by competitor, over rankings and endowments $E \ge 0$ only.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 11, Lemma 3 (proof p. 27)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

theorem lemma_3 {U : Type*} [DecidableEq U] (φ ψ : List U → ℝ → U → ℝ)
    (hφ : IsPrizeRule φ) (hψ : IsPrizeRule ψ)
    (hφEM : EndowmentMonotone φ) (hφCons : Consistent φ)
    (hψEM : EndowmentMonotone ψ) (hψCons : Consistent ψ)
    (h2 : ∀ (l : List U) (E : ℝ), IsRanking l → l.length = 2 → 0 ≤ E →
      ∀ i ∈ l, φ l E i = ψ l E i) :
    ∀ (l : List U) (E : ℝ), IsRanking l → 0 ≤ E → ∀ i ∈ l, φ l E i = ψ l E i := by sorry

end PrizeAlloc.Interval
