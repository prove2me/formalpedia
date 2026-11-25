-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_eq_one_3c2c8084ee96
-- name    : P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_eq_one_3c2c8084ee96
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:20.04613+00:00
-- url     : https://prove2.me/theorems/3e638757-6d3f-4abe-8fc4-cacbdd9c4eea
-- title:
--   P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow eq one 3c2c8084ee96: P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow eq one 3c2c8084ee96
-- statement:
--   The P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow eq one 3c2c8084ee96 construction uses the P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow eq one 3c2c8084ee96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L47-L49

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

theorem P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_eq_one_3c2c8084ee96 (m : ℕ) : ζQ l m ^ (l ^ m) = 1 := by sorry

alias «Formalism».«MainNotions».«N».«PreambleDegrees».«Loc».«ζQ_pow_eq_one» := P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_eq_one_3c2c8084ee96
