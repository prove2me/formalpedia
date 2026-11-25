-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_LocAinf___ne_one_c5617a838e7d
-- name    : P2M_Formalism_BasicNotions_LocAinf___ne_one_c5617a838e7d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:20.848812+00:00
-- url     : https://prove2.me/theorems/805b82c2-caf6-4577-92fa-80cd00eeff81
-- title:
--   P2 M Formalism Basic Notions Loc Ainf   ne one c5617a838e7d: P2 M Formalism Basic Notions Loc Ainf   ne one c5617a838e7d
-- statement:
--   The P2 M Formalism Basic Notions Loc Ainf   ne one c5617a838e7d construction uses the P2 M Formalism Basic Notions Loc Ainf   ne one c5617a838e7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L954-L998
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L954-L998

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementPC
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open Loc
open Formalism.BasicNotions.LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem P2M_Formalism_BasicNotions_LocAinf___ne_one_c5617a838e7d : AI.ε ≠ 1 := by sorry

alias «Formalism».«BasicNotions».«LocAinf».«ε_ne_one» := P2M_Formalism_BasicNotions_LocAinf___ne_one_c5617a838e7d
