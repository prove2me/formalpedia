-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_ucoord_prod_fundSystem_smul
-- name    : ReciprocityTheory.Cheb.ucoord_prod_fundSystem_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:41.171457+00:00
-- url     : https://prove2.me/theorems/f3f00c28-3360-436d-a490-537636cd3c35
-- title:
--   Cheb: ucoord prod fund System smul
-- statement:
--   The Cheb construction uses the ucoord prod fund System smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/UnitPart.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/UnitPart.lean#L39-L48

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.ucoord_prod_fundSystem_smul (f : Fin (rank E) → ℤ) (x : mixedSpace E)
    (hx : mixedEmbedding.norm x ≠ 0) (i : Fin (rank E)) :
    ucoord ((∏ i, (fundSystem E i) ^ (f i)) • x) i = ucoord x i + f i := by sorry
