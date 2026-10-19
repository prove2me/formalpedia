-- Prove2me | Theorems.Thm_PersuadeEarly_Private_lemma_2_2
-- name    : PersuadeEarly.Private.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:19.542413+00:00
-- url     : https://prove2.me/theorems/68f611c2-20db-4d7a-b666-65646754532f
-- title:
--   Lemma 2 (2), p. 35 — if $q_L<\bar F(p)$, $\arg\max_{t\ge p}\phi(t,p)=\bar F^{-1}(q_L)$
-- statement:
--   Under the standing assumptions, let $p\in[0,b]$ with $q_L<\bar F(p)$. Then the threshold $t=\bar F^{-1}(q_L)$ is the unique maximizer of $\phi(\cdot,p)$ over $t\ge p$:
--   $$\{t\ge p:\ \phi(s,p)\le\phi(t,p)\ \text{for all } s\ge p\}=\{\bar F^{-1}(q_L)\}.$$
--
--   In words: when the low inventory does not cover the customers above $p$, the best public threshold is the one at which the low-type firm exactly sells out in period 1.
--
--   **Formalization Note** The printed statement writes "$q$" for $q_L$, and "$\arg\max_t$" ranges over $t\ge p$ as in the lemma's quantifier. The set equality asserts both that the maximum is attained at $\bar F^{-1}(q_L)$ and that it is attained nowhere else.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 35, Lemma 2, part 2

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_AppendixA

open Set

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 35, Lemma 2, part 2: for any `p ∈ V`, if `qL < F̄(p)` then
`arg max_{t ≥ p} ϕ(t, p) = F̄^{-1}(qL)`.

**Formalization Note** The printed "q" is `qL`; the arg max ranges over `t ≥ p` (the lemma's
quantifier "for any p ∈ V with t ≥ p") and is stated as the set equality
`{maximizers} = {F̄^{-1}(qL)}`, so it asserts both attainment and uniqueness. -/
theorem lemma_2_2 (M : Model) (hM : M.Standing) :
    ∀ p ∈ Icc 0 M.b, M.qL < M.Fbar p →
      {t | p ≤ t ∧ ∀ s, p ≤ s → phi M s p ≤ phi M t p} = {M.FbarInv M.qL} := by sorry

end PersuadeEarly.Private
