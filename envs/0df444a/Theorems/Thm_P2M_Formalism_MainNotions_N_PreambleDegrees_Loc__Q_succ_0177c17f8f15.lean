-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_succ_0177c17f8f15
-- name    : P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_succ_0177c17f8f15
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:44.045701+00:00
-- url     : https://prove2.me/theorems/07ef1d72-eff3-5511-92e3-92d52820eb21
-- title:
--   P2 M Formalism Main Notions N Preamble Degrees Loc  Q succ 0177c17f8f15: P2 M Formalism Main Notions N Preamble Degrees Loc  Q succ 0177c17f8f15
-- statement:
--   The P2 M Formalism Main Notions N Preamble Degrees Loc  Q succ 0177c17f8f15 construction uses the P2 M Formalism Main Notions N Preamble Degrees Loc  Q succ 0177c17f8f15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L37-L40

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

theorem P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_succ_0177c17f8f15 (m : ℕ) : ζQ l (m + 1) ^ l = ζQ l m := by sorry

alias «Formalism».«MainNotions».«N».«PreambleDegrees».«Loc».«ζQ_succ» := P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_succ_0177c17f8f15
