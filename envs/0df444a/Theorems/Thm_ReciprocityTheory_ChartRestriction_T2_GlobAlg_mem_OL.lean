-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_T2_GlobAlg_mem_OL
-- name    : ReciprocityTheory.ChartRestriction.T2.GlobAlg.mem_OL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:30:51.886243+00:00
-- url     : https://prove2.me/theorems/2617ed66-1664-4972-8cd6-5ab69cb70ca3
-- title:
--   Glob Alg: mem OL
-- statement:
--   The Glob Alg construction uses the mem OL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L452-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L452-L453

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable [hT2Core : Fact Core]

theorem ReciprocityTheory.ChartRestriction.T2.GlobAlg.mem_OL {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by sorry
