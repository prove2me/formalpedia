-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_LocAinf__2_prim_5d93beb9df99
-- name    : P2M_Formalism_BasicNotions_LocAinf__2_prim_5d93beb9df99
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:24.830532+00:00
-- url     : https://prove2.me/theorems/842fb573-6f62-4088-ae6b-1c0c3a34329a
-- title:
--   P2 M Formalism Basic Notions Loc Ainf  2 prim 5d93beb9df99: P2 M Formalism Basic Notions Loc Ainf  2 prim 5d93beb9df99
-- statement:
--   The P2 M Formalism Basic Notions Loc Ainf  2 prim 5d93beb9df99 construction uses the P2 M Formalism Basic Notions Loc Ainf  2 prim 5d93beb9df99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L943-L952
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L943-L952

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

theorem P2M_Formalism_BasicNotions_LocAinf__2_prim_5d93beb9df99 : IsPrimitiveRoot (AI.ζ 2) (l ^ 2) := by sorry

alias «Formalism».«BasicNotions».«LocAinf».«ζ2_prim» := P2M_Formalism_BasicNotions_LocAinf__2_prim_5d93beb9df99
