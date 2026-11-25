-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_logEmbedding_prod_fundSystem
-- name    : ReciprocityTheory.Cheb.logEmbedding_prod_fundSystem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:50.735807+00:00
-- url     : https://prove2.me/theorems/bf943f76-0572-4b5c-8816-b202d240e5af
-- title:
--   Cheb: log Embedding prod fund System
-- statement:
--   The Cheb construction uses the log Embedding prod fund System property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/UnitPart.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/UnitPart.lean#L32-L37

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

theorem ReciprocityTheory.Cheb.logEmbedding_prod_fundSystem (f : Fin (rank E) → ℤ) :
    logEmbedding E (Additive.ofMul (∏ i, (fundSystem E i) ^ (f i))) =
      ∑ i, (f i : ℝ) • ((basisUnitLattice E i : unitLattice E) : logSpace E) := by sorry
