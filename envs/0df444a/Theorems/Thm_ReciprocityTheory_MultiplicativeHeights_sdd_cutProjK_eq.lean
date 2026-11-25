-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_cutProjK_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_cutProjK_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:27.343712+00:00
-- url     : https://prove2.me/theorems/8160f16f-62d8-44da-8e4d-426ab6e1fab8
-- title:
--   Multiplicative Heights: sdd cut Proj K eq
-- statement:
--   The Multiplicative Heights construction uses the sdd cut Proj K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L20-L20

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}

theorem ReciprocityTheory.MultiplicativeHeights.sdd_cutProjK_eq (x : Fin r → K) : cutProjK K r e x = projGe K r e x := by sorry
