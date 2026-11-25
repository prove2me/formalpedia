-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_Qi_comp_lmul_map_id
-- name    : PositivityTheory.PrwZar.Qi.comp_lmul_map_id
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:55.1551+00:00
-- url     : https://prove2.me/theorems/cd048f47-bd96-4523-b538-a46f1dbf554f
-- title:
--   Qi: comp lmul map id
-- statement:
--   The Qi construction uses the comp lmul map id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/CompLmulMapId.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/CompLmulMapId.lean#L14-L22

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_CompLmulMapId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem PositivityTheory.PrwZar.Qi.comp_lmul_map_id (ε : H →ₐ[K] K) (f : H →ₐ[K] H) (t : H ⊗[K] H) :
    f (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε) t)) =
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f ((Algebra.ofId K H).comp ε) t) := by sorry
