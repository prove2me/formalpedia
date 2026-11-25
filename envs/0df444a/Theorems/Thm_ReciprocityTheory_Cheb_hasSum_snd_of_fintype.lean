-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_hasSum_snd_of_fintype
-- name    : ReciprocityTheory.Cheb.hasSum_snd_of_fintype
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:41.954176+00:00
-- url     : https://prove2.me/theorems/5615fcf7-8c42-4c09-9166-6ff40853669a
-- title:
--   Cheb: has Sum snd of fintype
-- statement:
--   The Cheb construction uses the has Sum snd of fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/UnitPart.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/UnitPart.lean#L50-L56

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

theorem ReciprocityTheory.Cheb.hasSum_snd_of_fintype {α β : Type*} [Fintype α] {g : β → ℝ} (hg0 : ∀ b, 0 ≤ g b) {t : ℝ}
    (hg : HasSum g t) : HasSum (fun p : α × β => g p.2) (Fintype.card α * t) := by sorry
