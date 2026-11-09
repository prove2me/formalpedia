-- Prove2me | Theorems.Thm_SkipListConc_lemma_2_5
-- name    : SkipListConc.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:46.460996+00:00
-- url     : https://prove2.me/theorems/8a57a112-56aa-4997-86cd-d5cd0bc02fa4
-- title:
--   Lemma 2.5 — Morris domination $H_x(j)\ge M_x(j)$ (T2)
-- statement:
--   Fix $0<p<1$. Couple the height process of Definition 1.1 with the Morris chain of Definition 2.4 by one shared uniform per update: at update $j$ the gate opens if $U_j\le p^{H_x(j-1)}$ and the chain rises if $U_j\le p^{M_x(j-1)}$. Under this coupling, on every outcome,
--   $$
--   H_x(j)\ \ge\ M_x(j)\qquad\text{for every } j\ge1 .
--   $$
--
--   This is property (T2): every lower bound for the Morris counter is a lower bound for the height.
--
--   Differences from the source:
--   - encoding: there is a coupling with one shared uniform variable per update → the Morris chain `morris` is defined from the gate uniforms of the promotion noise; reason: this is the coupling of the proof; under the noise law it is Definition 2.4's chain with the right transition probabilities
--   - generalization: H_x(j) ≥ M_x(j) for 1 ≤ j ≤ f_x under the law of Definition 1.1 → for every j ≥ 1 and every realization ξ of the randomness (no law assumed); reason: the inequality is pointwise; the source's statement is the instance with the noise law and j ≤ f_x
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 2.4 and Lemma 2.5, p.14

import Mathlib
import Definitions.Def_SkipListConc_height
import Definitions.Def_SkipListConc_morris

namespace SkipListConc

/-- Lemma 2.5 (Morris domination, property (T2)) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 2.5, pp.14–15). Under the coupling that uses one shared uniform per update (the gate uniform
of Definition 1.1 also drives the Morris chain of Definition 2.4), `H_x(j) ≥ M_x(j)` for every
`j ≥ 1`, on every outcome.

**Formalization Note** The coupling is the definition `morris`. The inequality is pointwise and
holds for every noise realization `ξ`, so no law is assumed, and for every `j ≥ 1`, not only
`j ≤ f_x`. -/
theorem lemma_2_5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {K : ℕ} {α Ω : Type*}
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) :
    ∀ ω : Ω, ∀ j : ℕ, 1 ≤ j → morris p ξ x j ω ≤ height p ξ x j ω := by sorry

end SkipListConc
