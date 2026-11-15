-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_lemma_19
-- name    : UniversalNonstochastic.Main.Supplement.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:27:21.399943+00:00
-- url     : https://prove2.me/theorems/39ee2f6c-68c7-4d93-bd3b-a158efdb8f59
-- title:
--   Lemma 19 — the tail is at least $c_5\,2^{-\mu}$
-- statement:
--   Let $\mathbf m$ be the universal semimeasure, $\tau(t)=\mathbf m(\{n\in\mathbb N\mid n>t\})$ its tail, and $\mu(t)=\min\{K(n)\mid n\in\mathbb N,\ n>t\}$ the inverse busy beaver function. There is a constant $c_5>0$ such that for every real $t\ge0$, $\mu(t)$ is a natural number and
--   $$\tau(t)\ge c_5\,2^{-\mu(t)}.$$
--
--   This is the easy half of Andreev's estimate $-\log\tau\le\mu+O(1)$; it is used in the proofs of Theorems 5 and 11.
--
--   Differences from the source:
--   - encoding: µ(t) as a real exponent → ∃ μ : ℕ, µ(t) = μ, and the bound with μ; reason: µ is an ℕ∞-valued infimum; it is attained and finite, and asserting the witness avoids any default value of a conversion at ∞
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Lemma 19, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- Lemma 19, p.17: for some constant `c₅ > 0`, `τ(t) ≥ c₅ 2^{-µ(t)}` for every real `t ≥ 0`.
The conclusion also records that `µ(t)` is a natural number. -/
theorem lemma_19 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    ∃ c₅ : ℝ, 0 < c₅ ∧ ∀ t : ℝ, 0 ≤ t →
      ∃ μ : ℕ, invBusyBeaver U t = μ ∧ c₅ * (2 : ℝ) ^ (-(μ : ℝ)) ≤ tail m t := by sorry

end UniversalNonstochastic.Main.Supplement
