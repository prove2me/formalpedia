-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_imputations_of_inessential_essential
-- name    : TheoryOfGames.ThreePerson.imputations_of_inessential_essential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:24:22.28048+00:00
-- url     : https://prove2.me/theorems/06dc0fec-35c9-4b83-b0d7-5dea7871a5b6
-- title:
--   (31:I) — one imputation for an inessential game, infinitely many for an essential one
-- statement:
--   Let $v$ be a characteristic function of a zero-sum $n$-person game, i.e. $v$ satisfies (25:3:a)–(25:3:c). Consider the vector
--   $$\text{(31:9)}\quad \vec\alpha = \{\alpha_1, \dots, \alpha_n\}, \qquad \alpha_i = v((i)) \quad (i = 1, \dots, n).$$
--
--   1. If the game is inessential, then (31:9) is the only imputation.
--   2. If the game is essential, then there are infinitely many imputations, and (31:9) is not one of them.
--
--   The imputation set is thus a single point exactly in the inessential case, which drives the results (31:J)–(31:P) on one-element solutions.
--
--   **Formalization Note** The book adds that in the essential case the imputations form an $(n-1)$-dimensional continuum; only "infinitely many" (`Set.Infinite`) is formalized, the dimension claim is omitted.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 277–278, 31.2.1, (31:I), (31:9)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.ThreePerson

/-- (31:I), 31.2.1: for an inessential game the only imputation is (31:9)
`α = {v((1)), …, v((n))}`; for an essential game there are infinitely many imputations, and
(31:9) is not one of them. -/
theorem imputations_of_inessential_essential {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) :
    (TheoryOfGames.CharFun.IsInessential v → ∀ α : Fin n → ℝ, IsImputation v α ↔ α = fun i => v {i}) ∧
    (¬ TheoryOfGames.CharFun.IsInessential v →
      {α : Fin n → ℝ | IsImputation v α}.Infinite ∧ ¬ IsImputation v (fun i => v {i})) := by sorry

end TheoryOfGames.ThreePerson
