-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_localization_quotient_eq_height
-- name    : ReciprocityTheory.CA.ringKrullDim_localization_quotient_eq_height
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:01.718908+00:00
-- url     : https://prove2.me/theorems/d30d2d64-3896-4a76-8e91-99202ac2a8f7
-- title:
--   CA: ring Krull Dim localization quotient eq height
-- statement:
--   The CA construction uses the ring Krull Dim localization quotient eq height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L147-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L147-L235

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing

theorem ReciprocityTheory.CA.ringKrullDim_localization_quotient_eq_height {P : Type*} [CommRing P] (p q : Ideal P)
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) =
      ((q.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by sorry
