-- Prove2me | Theorems.Thm_PHarmUnionExhaustion
-- name    : PHarmUnionExhaustion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:31.307804+00:00
-- url     : https://prove2.me/theorems/1bcbdebc-a9e3-4e26-8ec0-971d8e871183
-- title:
--   PHarm Union Exhaustion: PHarm Union Exhaustion
-- statement:
--   Exhaustion: `p`-harmonicity on an increasing sequence of open sets, with one
--   and the same weak gradient, transfers to the union.
--
--   This is what assembles a family of ball-by-ball conclusions into one on a larger
--   domain.  A blow-up `u_r` is `p`-harmonic only on `ball 0 (ρ / r)`, never on
--   `Set.univ` for a fixed `r`, so a limit-passage lemma stated for a single fixed
--   domain can only be applied one ball at a time; this node turns the resulting family
--   of statements into `p`-harmonicity on the union.  The one substantive step is that a
--   compact subset of the union already lies in a single member, so a compactly
--   supported test function for the union is a test function for one member.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmUnionExhaustion.lean#L16-L73
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmUnionExhaustion.lean#L16-L73

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_PFluxContinuity
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_PHarmUnionExhaustion
import Theorems.Thm_PFluxContinuity
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false
set_option linter.unusedVariables false

theorem PHarmUnionExhaustion (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (Ω : ℕ → Set Plane) (u : Plane → ℝ) (g : Plane → Plane)
    (hmono : Monotone Ω) (h : ∀ n : ℕ, IsPHarm p (Ω n) u g) :
    IsPHarm p (⋃ n, Ω n) u g := by sorry
