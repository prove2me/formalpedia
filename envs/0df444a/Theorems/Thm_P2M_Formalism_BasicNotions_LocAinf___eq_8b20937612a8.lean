-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_LocAinf___eq_8b20937612a8
-- name    : P2M_Formalism_BasicNotions_LocAinf___eq_8b20937612a8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:05:29.530095+00:00
-- url     : https://prove2.me/theorems/b8c1d490-49d2-4221-94aa-714a7a1976e2
-- title:
--   P2 M Formalism Basic Notions Loc Ainf   eq 8b20937612a8: P2 M Formalism Basic Notions Loc Ainf   eq 8b20937612a8
-- statement:
--   The P2 M Formalism Basic Notions Loc Ainf   eq 8b20937612a8 construction uses the P2 M Formalism Basic Notions Loc Ainf   eq 8b20937612a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L842-L845
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L842-L845

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
open Loc NNReal
open Formalism.BasicNotions.LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem P2M_Formalism_BasicNotions_LocAinf___eq_8b20937612a8 : AI.μ = AI.π₁ * AI.ξ := by sorry

alias «Formalism».«BasicNotions».«LocAinf».«μ_eq» := P2M_Formalism_BasicNotions_LocAinf___eq_8b20937612a8
