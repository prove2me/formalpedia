-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_lemma_4
-- name    : UniversalNonstochastic.Main.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:29:25.477042+00:00
-- url     : https://prove2.me/theorems/98a3ea3d-d148-4fd3-97dd-a980a4488c10
-- title:
--   Lemma 4 — $\tau/c\le\sigma\le c\tau$
-- statement:
--   Let $\tau(t)=\mathbf m(\{n\in\mathbb N\mid n>t\})$ and $\sigma(t)=\mathbf m(\{n\in\mathbb N\mid K(n)>t\})$. For some constant $c>1$,
--   $$\tau(t)/c\le\sigma(t)\le c\,\tau(t)\qquad\text{for all real }t\ge0.$$
--
--   The universal mass of the objects of complexity above $t$ is thus comparable to the tail $\tau(t)$; this interprets Theorem 6 and is used in Theorems 13 and 15.
--
--   **Formalization Note** Both functions are taken on $\tau$'s domain $[0,\infty)$.
--
--   Differences from the source: none.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Lemma 4, eq. (3), p.6 (PDF p.6)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- Lemma 4, p.6, eq. (3): for some constant `c > 1`, `τ(t)/c ≤ σ(t) ≤ c τ(t)` for every real
`t ≥ 0`, where `σ(t) = m({n | K(n) > t})`. -/
theorem lemma_4 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    ∃ c : ℝ, 1 < c ∧ ∀ t : ℝ, 0 ≤ t →
      tail m t / c ≤ sigma m U t ∧ sigma m U t ≤ c * tail m t := by sorry

end UniversalNonstochastic.Main.Supplement
