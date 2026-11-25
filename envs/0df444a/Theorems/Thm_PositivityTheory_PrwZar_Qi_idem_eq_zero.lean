-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_Qi_idem_eq_zero
-- name    : PositivityTheory.PrwZar.Qi.idem_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:59.671059+00:00
-- url     : https://prove2.me/theorems/64229b7e-f79a-402c-a4eb-ee18acc8dedb
-- title:
--   Qi: idem eq zero
-- statement:
--   The Qi construction uses the idem eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiIdem.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiIdem.lean#L12-L39

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_WeilRepresentations_ZariskiDensity_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiIdem
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

theorem PositivityTheory.PrwZar.Qi.idem_eq_zero {K H : Type} [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    {f : H} (hf : IsIdempotentElem f) (h : ∀ x : H →ₐ[K] K, x f = 0) : f = 0 := by sorry
