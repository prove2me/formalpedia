-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_Qi_pw_charP
-- name    : PositivityTheory.PrwZar.Qi.pw_charP
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:52.609808+00:00
-- url     : https://prove2.me/theorems/5b7ba256-5819-4b87-863c-de32d318e5c3
-- title:
--   Qi: pw char P
-- statement:
--   The Qi construction uses the pw char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiCharP.lean#L15-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiCharP.lean#L15-L41

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_CompLmulMapId
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCharP
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

theorem PositivityTheory.PrwZar.Qi.pw_charP (p : ℕ) [Fact p.Prime] [CharP K p] (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K)
    (hL : CounitL Δ ε) (hR : CounitR Δ ε) (hmul : ∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b))
    (r : ℕ) {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε (p ^ r) x ∈ RingHom.ker ε ^ (2 ^ r) := by sorry
