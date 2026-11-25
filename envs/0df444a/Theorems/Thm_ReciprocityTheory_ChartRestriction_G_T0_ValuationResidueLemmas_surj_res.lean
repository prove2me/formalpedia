-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_surj_res
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.surj_res
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:28.531488+00:00
-- url     : https://prove2.me/theorems/234d1bb6-01ec-576d-b79f-4b07cb31d026
-- title:
--   Valuation Residue Lemmas: surj res
-- statement:
--   The Valuation Residue Lemmas construction uses the surj res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L240-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L240-L275

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.surj_res {K : Type} [Field K] [NumberField K] (ν : AddValuation K (WithTop ℤ))
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hnn : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ vRing ν)
    (hpos : ∀ a : 𝓞 K, 0 < ν (algebraMap (𝓞 K) K a) ↔ a ∈ la.asIdeal) :
    Function.Surjective ((residue (vRing ν)).comp
      ((algebraMap (𝓞 K) K).codRestrict (vRing ν) hnn)) := by sorry
