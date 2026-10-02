-- Prove2me | Theorems.Thm_SennottDP_Tauberian_continuous_sandwich_r
-- name    : SennottDP.Tauberian.continuous_sandwich_r
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T13:13:49.374271+00:00
-- url     : https://prove2.me/theorems/ca28769c-b296-4ea4-8909-9eab45354871
-- title:
--   Lemma A.4.1 — continuous s* ≤ r ≤ s with integrals within ε of 1
-- statement:
--   Let $r$ be the function of Fig. A.1. For every $\varepsilon > 0$ there exist continuous functions $s$ and $s^*$ such that $s^*(x) \le r(x) \le s(x)$ for $x \in (0,1)$ and
--   $$1 - \varepsilon \le \int_0^1 s^*(x)\,dx \le \int_0^1 s(x)\,dx \le 1 + \varepsilon.$$
--
--   The lemma lets a statement proved for continuous test functions be transferred to the discontinuous function $r$ by sandwiching.
--
--   **Formalization Note** The book says "continuous for $\alpha \in (0,1)$"; the statement requires continuity on the closed interval $[0,1]$. The functions drawn in Figs. A.2–A.3 have this property, and it is what the Weierstrass approximation step in the proof of Theorem A.4.2 needs. Continuity on $[0,1]$ also makes the integrals genuine (the functions are integrable).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 280, Lemma A.4.1, (A.27); Figs. A.1–A.3, pp. 281–282

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 280, Lemma A.4.1: given `ε > 0` there are continuous functions `s` and `s*`
with `s* ≤ r ≤ s` on `(0, 1)` and (A.27) `1 − ε ≤ ∫_0^1 s* ≤ ∫_0^1 s ≤ 1 + ε`.
Continuity is required on the closed interval `[0, 1]` (the functions of Figs. A.2–A.3 are), which
is what the Weierstrass step of the proof of Theorem A.4.2 uses. -/
theorem continuous_sandwich_r (ε : ℝ) (hε : 0 < ε) :
    ∃ s sstar : ℝ → ℝ, ContinuousOn s (Set.Icc 0 1) ∧ ContinuousOn sstar (Set.Icc 0 1) ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, sstar x ≤ r x ∧ r x ≤ s x) ∧
      1 - ε ≤ ∫ x in (0 : ℝ)..1, sstar x ∧
      ∫ x in (0 : ℝ)..1, sstar x ≤ ∫ x in (0 : ℝ)..1, s x ∧
      ∫ x in (0 : ℝ)..1, s x ≤ 1 + ε := by sorry

end SennottDP.Tauberian
