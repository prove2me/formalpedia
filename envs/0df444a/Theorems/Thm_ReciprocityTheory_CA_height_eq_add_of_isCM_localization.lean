-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_eq_add_of_isCM_localization
-- name    : ReciprocityTheory.CA.height_eq_add_of_isCM_localization
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:26.663369+00:00
-- url     : https://prove2.me/theorems/396d2042-91ee-4ff6-9316-f23ae4fa07f6
-- title:
--   CA: height eq add of is CM localization
-- statement:
--   The CA construction uses the height eq add of is CM localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyCM.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyCM.lean#L39-L52

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolySeq
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
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

theorem ReciprocityTheory.CA.height_eq_add_of_isCM_localization {S : Type*} [CommRing S] (𝔑 𝔔 : Ideal S) [𝔑.IsPrime]
    [𝔔.IsPrime] (h : IsCM (Localization.AtPrime 𝔑)) (hle : 𝔔 ≤ 𝔑) :
    𝔑.height = 𝔔.height + (𝔑.map (Ideal.Quotient.mk 𝔔)).height := by sorry
