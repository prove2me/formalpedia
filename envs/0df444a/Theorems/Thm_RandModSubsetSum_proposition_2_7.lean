-- Prove2me | Theorems.Thm_RandModSubsetSum_proposition_2_7
-- name    : RandModSubsetSum.proposition_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:21.133459+00:00
-- url     : https://prove2.me/theorems/25afe9be-2e84-4210-80da-306e54459186
-- title:
--   Proposition 2.7 — $|T_m(P)|=m!/\prod_a(mP(a))!$ and $mH(P)-|A|\log m\le\log|T_m(P)|\le mH(P)$
-- statement:
--   Let $A$ be a finite alphabet, $m\ge1$, and $P$ an exact type for length $m$ (an $m$-type). Then
--
--   $$|T_m(P)|=\frac{m!}{\prod_{a\in A}(mP(a))!},\qquad mH(P)-|A|\log_2 m\le\log_2|T_m(P)|\le mH(P).$$
--
--   In particular $\log_2|T_m(P)|=mH(P)+O(\log m)$: the entropy is the exponential rate of the number of words of a given type. The paper uses both bounds in every counting step of the second-moment analysis (13)–(15), (52) and in the partition and tag probabilities (17), (19).
--
--   **Formalization Note** For an $m$-type, $mP(a)$ is a natural number, written $\lfloor mP(a)\rfloor$.
--
--   Differences from the source:
--   - encoding: (mP(a))! for an exact type → (⌊mP(a)⌋₊)!; reason: mP(a) is a natural number for an m-type, so the floor changes nothing
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Proposition 2.7, p. 10

import Mathlib
import Definitions.Def_RandModSubsetSum_Types

open scoped BigOperators

namespace RandModSubsetSum

/-- **Proposition 2.7** (Lemma 8 in [Oze16]; type-class size). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Proposition 2.7, p. 10.

Let `A` be a finite alphabet, `m ≥ 1`, and `P` an exact type for length `m`. Then
`|T_m(P)| = m! / Π_a (m P(a))!` and `m H(P) − |A| log₂ m ≤ log₂ |T_m(P)| ≤ m H(P)`.

**Formalization Note.** Entropy and logarithms are in bits. `m P(a)` is a natural number for an
m-type, written `⌊m P(a)⌋₊`. -/
theorem proposition_2_7 {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (hm : 1 ≤ m)
    (P : α → ℝ) (hP : IsMType m P) :
    ((typeClass m P).card : ℝ) = (m.factorial : ℝ) / ∏ a, ((⌊(m : ℝ) * P a⌋₊).factorial : ℝ) ∧
    (m : ℝ) * entropy P - (Fintype.card α : ℝ) * Real.logb 2 m ≤
      Real.logb 2 ((typeClass m P).card : ℝ) ∧
    Real.logb 2 ((typeClass m P).card : ℝ) ≤ (m : ℝ) * entropy P := by sorry

end RandModSubsetSum
