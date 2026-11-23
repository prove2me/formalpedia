-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_103acde85a5f
-- name    : P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_103acde85a5f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:45.230111+00:00
-- url     : https://prove2.me/theorems/4334a455-0054-40e3-98a1-f882730f2cda
-- title:
--   P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow 103acde85a5f: P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow 103acde85a5f
-- statement:
--   The P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow 103acde85a5f construction uses the P2 M Formalism Main Notions N Preamble Degrees Loc  Q pow 103acde85a5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L42-L45

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

theorem P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_103acde85a5f (m k : ℕ) : ζQ l (m + k) ^ (l ^ k) = ζQ l m := by sorry

alias «Formalism».«MainNotions».«N».«PreambleDegrees».«Loc».«ζQ_pow» := P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_103acde85a5f
