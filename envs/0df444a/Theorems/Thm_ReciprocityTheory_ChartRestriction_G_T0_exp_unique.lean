-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exp_unique
-- name    : ReciprocityTheory.ChartRestriction.G.T0.exp_unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:58.948139+00:00
-- url     : https://prove2.me/theorems/021cb4d6-5e3a-4583-8884-f177e3fa3023
-- title:
--   T0: exp unique
-- statement:
--   The T0 construction uses the exp unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L143-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L143-L164

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)

theorem ReciprocityTheory.ChartRestriction.G.T0.exp_unique (la : HeightOneSpectrum (𝓞 K)) {m m' : ℤ} {u u' : Op D N la} (hu : IsUnit u)
    (hu' : IsUnit u')
    (h : (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u') : m = m' := by sorry
