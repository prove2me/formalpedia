-- Prove2me | Theorems.Thm_TimeLockedSales_Reform_proposition_1
-- name    : TimeLockedSales.Reform.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:52.492+00:00
-- url     : https://prove2.me/theorems/838249d2-1c77-44e5-89b8-67ce2384076d
-- title:
--   Proposition 1, p. 11 — purchase behavior at the two belief thresholds
-- statement:
--   Let the message $m$ sent to a customer have positive probability under an information policy $\sigma$, and let $e=\mathbb E[V\mid m,\sigma]$. With the thresholds $v^*<p<v^{**}$ from (5), her purchase decision is
--   $$a=1\text{ if }e\ge v^{**};\qquad a=S\text{ if }v^*\le e<v^{**};\qquad a=-1\text{ if }e<v^*.$$
--   These are the three response regimes used to interpret messages as recommendations.
--
--   **Formalization Note.** At $e=v^*$ the customer buys after an optimistic signal, and at $e=v^{**}$ she buys after either signal, because (2) resolves ties in favor of purchase. The printed intervals in (4) overlap at those endpoints. The theorem uses the half-open intervals dictated by (2). Boolean `true` denotes purchase or an optimistic signal. The history index $t$ denotes the first $t$ customers, so the statement concerns customer $t+1$. No focus-region assumption is needed.
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), p. 11, Proposition 1, (4)–(5); tie convention p. 10, (2)

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

namespace TimeLockedSales.Reform

/-- Proposition 1, p. 11; endpoints follow the tie-to-purchase rule (2). -/
theorem proposition_1 (P : Params) (hS : P.Standing)
    {M : Type} [Fintype M] (σ : InfoPolicy M) (t : ℕ) (ht : t < P.T) (m : M)
    (hm : 0 < msgProb P σ t m) :
    vStar P < P.p ∧ P.p < vStarStar P ∧
    (vStarStar P ≤ msgPosterior P σ t m →
      ∀ s : Bool, buysAt P σ t (law P σ t) s m) ∧
    (vStar P ≤ msgPosterior P σ t m →
      msgPosterior P σ t m < vStarStar P →
      ∀ s : Bool, (buysAt P σ t (law P σ t) s m ↔ s = true)) ∧
    (msgPosterior P σ t m < vStar P →
      ∀ s : Bool, ¬ buysAt P σ t (law P σ t) s m) := by sorry

end TimeLockedSales.Reform
