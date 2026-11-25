-- Prove2me | Theorems.Thm_UpperTheory_Small_zmod_two_quadratic_ne_zero
-- name    : UpperTheory.Small.zmod_two_quadratic_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:15.573377+00:00
-- url     : https://prove2.me/theorems/f23c575f-9b1f-59ad-9ccf-d5ec57532fae
-- title:
--   Small: zmod two quadratic ne zero
-- statement:
--   The Small construction uses the zmod two quadratic ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L99-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L99-L99

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ZmodTwoQuadraticNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain
variable {R : Ranks} (H : Host R)

theorem UpperTheory.Small.zmod_two_quadratic_ne_zero : ∀ v : ZMod 2, v ^ 2 - v + 1 ≠ 0 := by sorry
