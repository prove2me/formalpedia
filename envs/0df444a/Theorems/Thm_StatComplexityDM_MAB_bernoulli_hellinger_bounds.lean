-- Prove2me | Theorems.Thm_StatComplexityDM_MAB_bernoulli_hellinger_bounds
-- name    : StatComplexityDM.MAB.bernoulli_hellinger_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:11.008423+00:00
-- url     : https://prove2.me/theorems/41b5881f-9a15-4e73-acbf-06c23ec4fc2f
-- title:
--   Lemma A.7, p. 71 — D²_H(Ber(p), Ber(q)) ≤ (p−q)²(1/(p+q) + 1/(2−p−q)); D²_H(Ber(1/2+Δ), Ber(1/2)) ≤ 3Δ²; D²_H(Ber(1/2+Δ), Ber(1/2+2Δ)) ≤ 5Δ²
-- statement:
--   Let $D^2_{\mathrm{H}}(P,Q) = \sum_y (\sqrt{P(y)} - \sqrt{Q(y)})^2$ be the squared Hellinger distance and $\mathrm{Ber}(q)$ the Bernoulli distribution with mean $q$. Then:
--
--   1. For all $p, q \in [0,1]$,
--   $$
--   D^2_{\mathrm{H}}\bigl(\mathrm{Ber}(p), \mathrm{Ber}(q)\bigr) \le (p - q)^2 \cdot \left( \frac{1}{p + q} + \frac{1}{1 - p + 1 - q} \right).
--   $$
--   2. For all $\Delta \in (0, \tfrac12)$, $\ D^2_{\mathrm{H}}\bigl(\mathrm{Ber}(\tfrac12 + \Delta), \mathrm{Ber}(\tfrac12)\bigr) \le 3\Delta^2$.
--   3. For all $\Delta \in (0, \tfrac14)$, $\ D^2_{\mathrm{H}}\bigl(\mathrm{Ber}(\tfrac12 + \Delta), \mathrm{Ber}(\tfrac12 + 2\Delta)\bigr) \le 5\Delta^2$.
--
--   The second bound is the information property of the hard family in the multi-armed bandit lower bound (Proposition 5.3); the third enters the gap-dependent variant.
--
--   **Formalization Note** The Hellinger distance carries no factor $\tfrac12$, as in the paper's (5). At $p = q = 0$ (resp. $p = q = 1$) the term $1/(p+q)$ (resp. $1/(1-p+1-q)$) has a zero denominator; Lean evaluates $x/0 = 0$, and the left side is also $0$ there, so the first bound is stated for all of $[0,1]^2$ as on the page.
-- source:
--   arXiv:2112.13487v3, Lemma A.7, p. 71

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_MAB_Bernoulli

namespace StatComplexityDM.MAB

open FoundationsRL.GeneralDM

/-- Lemma A.7 (arXiv:2112.13487v3, p. 71), divergence for Bernoulli distributions:
for all `p, q ∈ [0, 1]`, `D²_H(Ber(p), Ber(q)) ≤ (p − q)² · (1/(p + q) + 1/(1 − p + 1 − q))`;
for all `Δ ∈ (0, 1/2)`, `D²_H(Ber(1/2 + Δ), Ber(1/2)) ≤ 3Δ²`; and for all `Δ ∈ (0, 1/4)`,
`D²_H(Ber(1/2 + Δ), Ber(1/2 + 2Δ)) ≤ 5Δ²`. `D²_H` is `hellingerSq` (no factor `1/2`, (5), p. 10).
At `p = q = 0` and `p = q = 1` a denominator vanishes; Lean's `x / 0 = 0` makes the right side `0`,
which the left side also equals there. -/
theorem bernoulli_hellinger_bounds :
    (∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      hellingerSq (ber p) (ber q) ≤ (p - q) ^ 2 * (1 / (p + q) + 1 / (1 - p + (1 - q)))) ∧
    (∀ Δ : ℝ, 0 < Δ → Δ < 1 / 2 →
      hellingerSq (ber (1 / 2 + Δ)) (ber (1 / 2)) ≤ 3 * Δ ^ 2) ∧
    (∀ Δ : ℝ, 0 < Δ → Δ < 1 / 4 →
      hellingerSq (ber (1 / 2 + Δ)) (ber (1 / 2 + 2 * Δ)) ≤ 5 * Δ ^ 2) := by sorry

end StatComplexityDM.MAB
