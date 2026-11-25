-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_transL
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.transL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:54.857731+00:00
-- url     : https://prove2.me/theorems/fe0f9759-3e41-4cf3-b660-266ae39dcef4
-- title:
--   Tor: trans L
-- statement:
--   The Tor construction uses the trans L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L35-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.transL {B Y Z : Scheme.{0}} (a : Z ⟶ Y) (q : Y ⟶ B) (U U' : B.Opens) (g : Γ(B, U ⊓ U')ˣ)
    (u : Γ(Y, q ⁻¹ᵁ U)ˣ) (u' : Γ(Y, q ⁻¹ᵁ U')ˣ)
    (h : res (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U')) u' =
      pullU q _ g * res (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U)) u) :
    res (a.preimage_mono (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U'))) (pullU a _ u') =
      pullU a _ (pullU q _ g) * res (a.preimage_mono (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U))) (pullU a _ u) := by sorry
