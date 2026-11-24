-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_norm_embZ
-- name    : ReciprocityTheory.Cheb.norm_embZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:58.879477+00:00
-- url     : https://prove2.me/theorems/fb2380e7-b7ac-4318-97af-cb46cf9cf91d
-- title:
--   Cheb: norm emb Z
-- statement:
--   The Cheb construction uses the norm emb Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L51-L54

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
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

theorem ReciprocityTheory.Cheb.norm_embZ (α : 𝓞 E) : mixedEmbedding.norm (embZ α) = |((Algebra.norm ℤ α : ℤ) : ℝ)| := by sorry
