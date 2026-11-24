-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_Qi_counit_pw
-- name    : PositivityTheory.PrwZar.Qi.counit_pw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:25.462795+00:00
-- url     : https://prove2.me/theorems/95de01d1-b0ad-4764-b8af-3db7b6accbbd
-- title:
--   Qi: counit pw
-- statement:
--   The Qi construction uses the counit pw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/CompLmulMapId.lean#L24-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/CompLmulMapId.lean#L24-L46

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

theorem PositivityTheory.PrwZar.Qi.counit_pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ) :
    ε.comp (pw Δ ε n) = ε := by sorry
