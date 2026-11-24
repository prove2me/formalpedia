-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_nzIdeal_ne_zero
-- name    : ReciprocityTheory.Cheb.nzIdeal_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:42.970502+00:00
-- url     : https://prove2.me/theorems/0df7bdd0-8e68-4250-90ce-7ebe5a03c181
-- title:
--   Cheb: nz Ideal ne zero
-- statement:
--   The Cheb construction uses the nz Ideal ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L12-L13

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.nzIdeal_ne_zero (a : NZIdeal E) : a.1 ≠ 0 := by sorry
