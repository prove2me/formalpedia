-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_exists_undominated_iff_inessential
-- name    : TheoryOfGames.ThreePerson.exists_undominated_iff_inessential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:24:22.92667+00:00
-- url     : https://prove2.me/theorems/cbbed635-cacf-4ea0-846f-30a3999a01c8
-- title:
--   (31:M) — an undominated imputation exists iff the game is inessential
-- statement:
--   Let $v$ be a characteristic function of a zero-sum $n$-person game, satisfying (25:3:a)–(25:3:c). Then
--   $$\exists\ \text{imputation } \vec\alpha \text{ such that never } \vec\alpha' \succ \vec\alpha \ (\vec\alpha' \text{ an imputation}) \iff \text{the game is inessential.}$$
--
--   Undominated imputations are what later literature calls the core; the statement says that for zero-sum games the core is nonempty only in the trivial case.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 280, 31.2.3, (31:M)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.ThreePerson

/-- (31:M), 31.2.3: an imputation `α`, for which never `α' ⊱ α` (`α'` an imputation), exists if and
only if the game is inessential. -/
theorem exists_undominated_iff_inessential {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) :
    (∃ α : Fin n → ℝ, IsImputation v α ∧
        ∀ α' : Fin n → ℝ, IsImputation v α' → ¬ Dominates v α' α) ↔
      TheoryOfGames.CharFun.IsInessential v := by sorry

end TheoryOfGames.ThreePerson
