-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_uniq
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tan_uniq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:50.262395+00:00
-- url     : https://prove2.me/theorems/aea777c0-5f4a-447b-a7f8-855a4580963e
-- title:
--   Chart: tan uniq
-- statement:
--   The Chart construction uses the tan uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L157-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L157-L194

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] [Algebra.FinitePresentation S B]
  {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

theorem ReciprocityTheory.ChartRestriction.G.Chart.tan_uniq (h₁ h₂ : B →ₐ[S] DualNumber A) (t₁ : IsTanAt e h₁) (t₂ : IsTanAt e h₂)
    (heq : (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₁ = (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₂) :
    ∃ m ∈ M, (scaleS (algebraMap S A m)).comp h₁ = (scaleS (algebraMap S A m)).comp h₂ := by sorry
