-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_primitive_9c1c10a2e5e5
-- name    : P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_primitive_9c1c10a2e5e5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:11.773201+00:00
-- url     : https://prove2.me/theorems/e61d92cf-7002-4085-a61b-a1a6e9f6b805
-- title:
--   P2 M Formalism Main Notions N Preamble Degrees Loc  Q primitive 9c1c10a2e5e5: P2 M Formalism Main Notions N Preamble Degrees Loc  Q primitive 9c1c10a2e5e5
-- statement:
--   The P2 M Formalism Main Notions N Preamble Degrees Loc  Q primitive 9c1c10a2e5e5 construction uses the P2 M Formalism Main Notions N Preamble Degrees Loc  Q primitive 9c1c10a2e5e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L51-L59

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.PreambleDegrees Formalism.MainNotions.N.PreambleDegrees.Loc
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Polynomial
variable {l : ℕ} [Fact l.Prime]
variable (l)

theorem P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_primitive_9c1c10a2e5e5 (m : ℕ) : IsPrimitiveRoot (ζQ l m) (l ^ m) := by sorry

alias «Formalism».«MainNotions».«N».«PreambleDegrees».«Loc».«ζQ_primitive» := P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_primitive_9c1c10a2e5e5
