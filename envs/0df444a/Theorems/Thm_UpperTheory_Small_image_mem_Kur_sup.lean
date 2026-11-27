-- Prove2me | Theorems.Thm_UpperTheory_Small_image_mem_Kur_sup
-- name    : UpperTheory.Small.image_mem_Kur_sup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:47.367316+00:00
-- url     : https://prove2.me/theorems/fa36392d-f347-4c2f-b295-4f963f23b14d
-- title:
--   Small: image mem Kur sup
-- statement:
--   The Small construction uses the image mem Kur sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L48-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ZmodTwoQuadraticNeZero.lean#L48-L77

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

theorem UpperTheory.Small.image_mem_Kur_sup {l : ℕ} [Fact l.Prime] (J : H.E →+* Om l) {s : ℕ} (hs : H.condN.factorization l ≤ s) (x : H.E) :
    J x ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by sorry
