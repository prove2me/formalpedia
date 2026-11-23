-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_LocAinf_isUnit_inclW___dfbc296eb1fb
-- name    : P2M_Formalism_BasicNotions_LocAinf_isUnit_inclW___dfbc296eb1fb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:10.660224+00:00
-- url     : https://prove2.me/theorems/2fe66e38-a5f4-4d6e-af5a-04ee58313b54
-- title:
--   P2 M Formalism Basic Notions Loc Ainf is Unit incl W   dfbc296eb1fb: P2 M Formalism Basic Notions Loc Ainf is Unit incl W   dfbc296eb1fb
-- statement:
--   The P2 M Formalism Basic Notions Loc Ainf is Unit incl W   dfbc296eb1fb construction uses the P2 M Formalism Basic Notions Loc Ainf is Unit incl W   dfbc296eb1fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L1000-L1015
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L1000-L1015

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

theorem P2M_Formalism_BasicNotions_LocAinf_isUnit_inclW___dfbc296eb1fb : IsUnit (inclW l AI.ξ) := by sorry

alias «Formalism».«BasicNotions».«LocAinf».«isUnit_inclW_ξ» := P2M_Formalism_BasicNotions_LocAinf_isUnit_inclW___dfbc296eb1fb
