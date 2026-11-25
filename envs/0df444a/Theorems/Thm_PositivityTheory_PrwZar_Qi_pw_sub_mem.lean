-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_Qi_pw_sub_mem
-- name    : PositivityTheory.PrwZar.Qi.pw_sub_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:35.69321+00:00
-- url     : https://prove2.me/theorems/2ab9ddbf-0c8d-5bf3-89fd-1b5564ee4b6d
-- title:
--   Qi: pw sub mem
-- statement:
--   The Qi construction uses the pw sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/CompLmulMapId.lean#L48-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/CompLmulMapId.lean#L48-L90

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

theorem PositivityTheory.PrwZar.Qi.pw_sub_mem (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ)
    {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε n x - (n : H) * x ∈ RingHom.ker ε ^ 2 := by sorry
