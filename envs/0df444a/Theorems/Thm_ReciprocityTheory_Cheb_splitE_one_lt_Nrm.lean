-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitE_one_lt_Nrm
-- name    : ReciprocityTheory.Cheb.splitE_one_lt_Nrm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:19.757242+00:00
-- url     : https://prove2.me/theorems/f8f54ff7-63cd-4f2d-94a5-8a03c745f7f4
-- title:
--   Cheb: split E one lt Nrm
-- statement:
--   The Cheb construction uses the split E one lt Nrm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L69-L75

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem ReciprocityTheory.Cheb.splitE_one_lt_Nrm (q : Prm E) : 1 < Nrm q := by sorry
