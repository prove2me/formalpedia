-- Prove2me | Theorems.Thm_UpperTheory_Small_card_quot_ne_two
-- name    : UpperTheory.Small.card_quot_ne_two
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:10:09.276803+00:00
-- url     : https://prove2.me/theorems/4cf7f211-f9f7-5ecf-b0d4-4c6de1bc24be
-- title:
--   Small: card quot ne two
-- statement:
--   The Small construction uses the card quot ne two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L101-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L101-L129

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

theorem UpperTheory.Small.card_quot_ne_two (P : HeightOneSpectrum (𝓞 H.E)) : Nat.card (𝓞 H.E ⧸ P.asIdeal) ≠ 2 := by sorry
