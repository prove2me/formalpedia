-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_card_G
-- name    : ReciprocityTheory.ChartRestriction.L1.card_G
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:45.711623+00:00
-- url     : https://prove2.me/theorems/8947aab4-91ad-53a1-b3f3-85cdaaccdc00
-- title:
--   L1: card G
-- statement:
--   The L1 construction uses the card G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedCardG.lean#L109-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedCardG.lean#L109-L218

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open CardG

theorem ReciprocityTheory.ChartRestriction.L1.card_G (L : PeriodPair) (β : ℂ) (hβ : MulStable L β) (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : Complex.normSq β = ((p * M : ℕ) : ℝ)) (hM : ¬ p ∣ M) (T : Finset ℂ)
    (hT : IsHalfReps L (p : ℂ) T) :
    2 * (T.filter (fun P => β * P ∈ L.lattice)).card + 1 = p := by sorry
