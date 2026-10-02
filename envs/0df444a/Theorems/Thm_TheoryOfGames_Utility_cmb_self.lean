-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_cmb_self
-- name    : TheoryOfGames.Utility.cmb_self
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T01:22:40.463971+00:00
-- url     : https://prove2.me/theorems/430bd26a-1d24-4638-b7d2-c798f766f844
-- title:
--   (A:T) — always (1 − γ)u + γu = u
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C). For every utility $u$ and every $0 < \gamma < 1$,
--   $$(1-\gamma)u + \gamma u = u .$$
--
--   Idempotence of the combining operation is not among the axioms; it is a consequence of them. It is needed to extend the linearity of the utility function to the case $u = v$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 626–627, (A:T)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- (A:T): always `(1 − γ)u + γu = u`. -/
theorem cmb_self {U : Type*} (S : UtilitySystem U) (γ : OpenUnit) (u : U) :
    S.cmb γ u u = u := by sorry

end TheoryOfGames.Utility
