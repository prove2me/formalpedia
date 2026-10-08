-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_exists_dominating_not_dominated
-- name    : TheoryOfGames.ThreePerson.exists_dominating_not_dominated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:24:33.91972+00:00
-- url     : https://prove2.me/theorems/dda8f660-7451-4350-bb9b-323bf239560b
-- title:
--   (31:L) — in an essential game every imputation is dominated by one it does not dominate
-- statement:
--   Let $v$ be a characteristic function of an essential zero-sum $n$-person game (so $v$ satisfies (25:3:a)–(25:3:c) and its reduced form is not identically $0$), and let $\vec\alpha$ be an imputation. Then there exists an imputation $\vec\beta$ with
--   $$\vec\beta \succ \vec\alpha \quad\text{but not}\quad \vec\alpha \succ \vec\beta .$$
--
--   In an essential game no imputation is safe from domination; this is the key to (31:M) and (31:N).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 279, 31.2.2, (31:L)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.ThreePerson

/-- (31:L), 31.2.2: given an essential game and an imputation `α`, there exists an imputation
`β` such that `β ⊱ α` but not `α ⊱ β`. -/
theorem exists_dominating_not_dominated {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) (hess : ¬ TheoryOfGames.CharFun.IsInessential v) (α : Fin n → ℝ)
    (hα : IsImputation v α) :
    ∃ β : Fin n → ℝ, IsImputation v β ∧ Dominates v β α ∧ ¬ Dominates v α β := by sorry

end TheoryOfGames.ThreePerson
