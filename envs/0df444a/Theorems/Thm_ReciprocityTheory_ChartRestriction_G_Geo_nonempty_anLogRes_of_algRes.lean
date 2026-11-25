-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_nonempty_anLogRes_of_algRes
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.nonempty_anLogRes_of_algRes
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:47.530256+00:00
-- url     : https://prove2.me/theorems/bf3c1d21-21de-50f1-bf22-41b2a4215c8f
-- title:
--   Geo: nonempty an Log Res of alg Res
-- statement:
--   The Geo construction uses the nonempty an Log Res of alg Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterAlgRes.lean#L27-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterAlgRes.lean#L27-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterAlgRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.nonempty_anLogRes_of_algRes (P J : Ideal (MRing ι)) (e : ℕ)
    (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P)
    (hPC : ∀ f : MRing ι, MvPolynomial.map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) (pC J) e) : Nonempty (AnLogRes P J e) := by sorry
