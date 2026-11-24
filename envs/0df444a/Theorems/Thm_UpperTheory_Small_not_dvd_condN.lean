-- Prove2me | Theorems.Thm_UpperTheory_Small_not_dvd_condN
-- name    : UpperTheory.Small.not_dvd_condN
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:11:39.384211+00:00
-- url     : https://prove2.me/theorems/c59fff17-9e98-4824-9e1a-c28e5e060357
-- title:
--   Small: not dvd cond N
-- statement:
--   The Small construction uses the not dvd cond N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L16-L22

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

theorem UpperTheory.Small.not_dvd_condN {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q) (hd : l ≠ H.d) : ¬ l ∣ H.condN := by sorry
