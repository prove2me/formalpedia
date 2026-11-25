-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ofLin_fst
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.ofLin_fst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:53:56.248795+00:00
-- url     : https://prove2.me/theorems/802715dd-cb0b-4fa2-8fd3-9d81c5cb1c50
-- title:
--   Chart: of Lin fst
-- statement:
--   The Chart construction uses the of Lin fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L72-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L72-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
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
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]
variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
variable [Module B A] [IsScalarTower S B A] (hsm : ∀ (b : B) (a : A), b • a = e b * a)

theorem ReciprocityTheory.ChartRestriction.G.Chart.ofLin_fst (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).fst = e b := by sorry
