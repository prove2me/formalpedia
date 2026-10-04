-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_cmb_lt_cmb_of_lt
-- name    : TheoryOfGames.Utility.cmb_lt_cmb_of_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T01:03:43.884581+00:00
-- url     : https://prove2.me/theorems/b89c7571-61db-4bb3-9dd8-26505b861c9a
-- title:
--   (A:A) — combinations of u < v increase with the weight on v
-- statement:
--   Let $U$ be a system of utilities satisfying the axioms (3:A)–(3:C) of 3.6.1. If $u < v$, then for weights $0 < \alpha < \beta < 1$,
--   $$(1-\alpha)u + \alpha v < (1-\beta)u + \beta v .$$
--
--   This is the first step of the Appendix's derivation: the combination of two ordered utilities moves strictly upward as weight is shifted toward the better one. It gives the monotony in (A:B).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 618, (A:A)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- (A:A): if `u < v`, then `α < β` implies `(1 − α)u + αv < (1 − β)u + βv`. -/
theorem cmb_lt_cmb_of_lt {U : Type*} (S : UtilitySystem U) {u v : U} (huv : S.lt u v)
    {α β : OpenUnit} (hαβ : (α : ℝ) < (β : ℝ)) :
    S.lt (S.cmb α u v) (S.cmb β u v) := by sorry

end TheoryOfGames.Utility
