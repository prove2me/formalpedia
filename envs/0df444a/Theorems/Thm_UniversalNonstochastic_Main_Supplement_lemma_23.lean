-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_lemma_23
-- name    : UniversalNonstochastic.Main.Supplement.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:34:35.179998+00:00
-- url     : https://prove2.me/theorems/da417a3c-0d25-45a4-91a6-259ee384f013
-- title:
--   Lemma 23 — complex intervals have small universal mass
-- statement:
--   An interval is a set $I=\{n\in\mathbb N\mid a<n\le b\}$ with $a,b\in\mathbb N_0$. There is a constant $c_{62}$ such that for all $s\in\mathbb N_0$ and all intervals $I$ with $K(n)>s$ for every $n\in I$,
--   $$\mathbf m(I)\le2^{-s+c_{62}\log(s+2)}.\qquad(49)$$
--
--   The lemma covers a middle ground between Andreev's estimate (intervals $(a,\infty)$) and the Epstein–Levin results (arbitrary sets); it supports the upper bound (28) of Theorem 14.
--
--   Differences from the source: none.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Lemma 23, eq. (49), p.25 (PDF p.25); intervals defined on p.25

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity

namespace UniversalNonstochastic.Main.Supplement

/-- Lemma 23, p.25, eq. (49): there is a constant `c₆₂` such that for all `s ∈ ℕ₀` and all
intervals `I = {n ∈ ℕ | a < n ≤ b}` (`a, b ∈ ℕ₀`) with `K(n) > s` for all `n ∈ I`,
`m(I) ≤ 2^{-s + c₆₂ log₂(s+2)}`. -/
theorem lemma_23 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    ∃ c₆₂ : ℝ, ∀ s a b : ℕ,
      (∀ n : ℕ+, a < (n : ℕ) → (n : ℕ) ≤ b → (s : ℕ∞) < Kobj U n) →
        mass m {n : ℕ+ | a < (n : ℕ) ∧ (n : ℕ) ≤ b} ≤
          (2 : ℝ) ^ (-(s : ℝ) + c₆₂ * Real.logb 2 ((s : ℝ) + 2)) := by sorry

end UniversalNonstochastic.Main.Supplement
