-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_proj_eq_zero_iff
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_proj_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:41.770803+00:00
-- url     : https://prove2.me/theorems/6f5086cd-4658-467a-bff9-b10058188fcc
-- title:
--   Multiplicative Heights: sdd proj eq zero iff
-- statement:
--   The Multiplicative Heights construction uses the sdd proj eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean#L22-L31

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

theorem ReciprocityTheory.MultiplicativeHeights.sdd_proj_eq_zero_iff (x : Fin r → K) : projGe K r e x = 0 ↔ x ∈ cutSub K r e := by sorry
